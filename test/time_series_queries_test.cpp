#include "ARCEDB/comparison/rgsw_ciphertext.h"
#include "ARCEDB/comparison/comparable.h"
#include "ARCEDB/conversion/packlwes.h"
#include "ARCEDB/comparison/batch_bootstrap.h"
#include "ARCEDB/utils/serialize.h"
#include "ARCEDB/conversion/repack.h"
#include <random>
#include <chrono>
#include <omp.h>
#include <unistd.h>
#include <iomanip>

using namespace arcedb;
using namespace seal;

struct QueryTime {
    double filtering_time;
    double conversion_time;
    double aggregation_time;
    
    QueryTime(double f = 0, double c = 0, double a = 0) 
        : filtering_time(f), conversion_time(c), aggregation_time(a) {}
};

/**
    SELECT COUNT(*) FROM MedicalHistory
    WHERE (systolic < 90 OR diastolic < 50 OR
        weight_gain > 2 OR heart_rate < 40
        OR heart_rate > 90) AND (time BETWEEN
        2021:07:01:00:00 AND 2021:08:01:00:00)
    @param[in] num The size of the database.
*/
QueryTime time_series_query1(size_t num)
{
    QueryTime times;
    std::cout << "Time-Series SQL Query1 Test: "<< std::endl;
    std::cout << "--------------------------------------------------------"<< std::endl;
    std::cout << "Records: " << num << std::endl;
    std::random_device seed_gen;
    std::default_random_engine engine(seed_gen());
    using P = Lvl1;
    TFHESecretKey sk;
    TFHEEvalKey ek;
    using bkP = Lvl01;
    using iksP = Lvl10;
    std::uniform_int_distribution<uint32_t> message(1, P::n-1);
    ek.emplacebkfft<bkP>(sk);
    ek.emplaceiksk<iksP>(sk);
    ek.emplacebkfft<Lvl02>(sk);
    std::vector<uint64_t> systolic(num), diastolic(num),weight_gain(num),heart_rate(num);
    std::vector<std::vector<uint64_t>> time_values(num);
    std::vector<uint64_t> full_time_values(num);
    uint32_t time_values_width = 7;
    std::vector<TRLWELvl1> systolic_cipher(num), diastolic_cipher(num), weight_gain_cipher(num), heart_rate_cipher(num);
    std::vector<std::vector<TRLWELvl1>> time_values_cipher(num);

    TRGSWLvl1 predicate1_cipher, predicate2_cipher, predicate3_cipher, predicate4_cipher, predicate5_cipher;
    std::vector<TRGSWLvl1> predicate6_cipher(time_values_width), predicate7_cipher(time_values_width);
    exponent_encrypt_rgsw<P>(90, predicate1_cipher, sk, true);
    exponent_encrypt_rgsw<P>(50, predicate2_cipher, sk, true);
    exponent_encrypt_rgsw<P>(2, predicate3_cipher, sk, true);
    exponent_encrypt_rgsw<P>(40, predicate4_cipher, sk, true);
    exponent_encrypt_rgsw<P>(90, predicate5_cipher, sk, true);

    std::vector<uint64_t> predicate6(time_values_width);
    std::vector<uint64_t> predicate7(time_values_width);
    uint64_t full_predicate6 = 1625068800000, full_predicate7 = 1627747200000;
    exponent_encrypt_rgsw<P>(full_predicate6, 64, predicate6_cipher, sk, true);
    exponent_encrypt_rgsw<P>(full_predicate7, 64, predicate7_cipher, sk, true);
    
    // Start sql evaluation
    std::vector<TLWELvl1> filter_res(num);
    std::vector<TLWELvl2> aggregation_res(num);
    TLWELvl2 count_res;

    #pragma omp parallel for num_threads(48)
    for (size_t i = 0; i < num; i++)
    {
        // Generate data
        systolic[i] = i % 2 == 0 ? 100 : message(engine);
        diastolic[i] = i % 2 == 0 ? 20 : message(engine);
        weight_gain[i] = i % 2 == 0 ? 1 : message(engine);
        heart_rate[i] = i % 2 == 0 ? 60 : message(engine);

        time_values[i].resize(time_values_width);

        full_time_values[i] =1627000000000 + i;
        
        // Encrypt
        exponent_encrypt<P>(systolic[i], systolic_cipher[i], sk);
        exponent_encrypt<P>(diastolic[i], diastolic_cipher[i], sk);
        exponent_encrypt<P>(weight_gain[i], weight_gain_cipher[i], sk);
        exponent_encrypt<P>(heart_rate[i], heart_rate_cipher[i], sk);
        time_values_cipher[i].resize(time_values_width);
        exponent_encrypt<P>(full_time_values[i], 64, time_values_cipher[i], sk);

    }

    std::chrono::system_clock::time_point start, end;
    uint64_t query_res = 0;
    start = std::chrono::system_clock::now();

    #pragma omp parallel for num_threads(48)
    for (size_t i = 0; i < num; i++)
    {
        
        TLWELvl1 pre_res;
        /*
        systolic < 90 OR diastolic < 50 OR
        weight_gain > 2 OR heart_rate < 40
        OR heart_rate > 90) AND (time BETWEEN
        2021:07:01:00:00 AND 2021:08:01:00:00
        */
        less_than_tfhepp(systolic_cipher[i], predicate1_cipher, filter_res[i], sk);
        less_than_tfhepp(diastolic_cipher[i], predicate2_cipher, pre_res, sk);
        TFHEpp::HomOR(filter_res[i], filter_res[i], pre_res, ek);
        greater_than_tfhepp(weight_gain_cipher[i], predicate3_cipher, pre_res, sk);
        TFHEpp::HomOR(filter_res[i], filter_res[i], pre_res, ek);
        less_than_tfhepp(heart_rate_cipher[i], predicate4_cipher, pre_res, sk);
        TFHEpp::HomOR(filter_res[i], filter_res[i], pre_res, ek);
        greater_than_tfhepp(heart_rate_cipher[i], predicate5_cipher, pre_res, sk);
        TFHEpp::HomOR(filter_res[i], filter_res[i], pre_res, ek);     
        greater_than_tfhepp(time_values_cipher[i], predicate6_cipher, time_values_width, pre_res, ek, sk);
        TFHEpp::HomAND(filter_res[i], filter_res[i], pre_res, ek);
        less_than_tfhepp(time_values_cipher[i], predicate7_cipher, time_values_width, pre_res, ek, sk);
        lift_and_and(filter_res[i], pre_res, aggregation_res[i], 48, ek, sk);

        
    }
    end = std::chrono::system_clock::now();
    times.filtering_time = std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count();

    count_res = aggregation_res[0];
    for (size_t i = 1; i < num; i++)
    {
        for (size_t j = 0; j <= Lvl2::n; j++)
        {
            count_res[j] += aggregation_res[i][j];
        }

    }
    
    // Conversion time
    start = std::chrono::system_clock::now();
    // 这里没有实际的转换操作，但为了保持一致性，我们仍然记录时间
    end = std::chrono::system_clock::now();
    times.conversion_time = std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count();

    uint64_t plain_result = 0;
    for (size_t i = 0; i < num; i++)
    {
        bool filter_no_time = false;
        if (systolic[i] < 90 || diastolic[i] < 50 || weight_gain[i] > 2|| heart_rate[i] < 40 || heart_rate[i] > 90)
        {
            filter_no_time = true;
        }

        if (filter_no_time && (full_time_values[i] > full_predicate6) && (full_time_values[i] < full_predicate7))
        {
            plain_result += 1;
        }

    }
    
    // Aggregation time
    start = std::chrono::system_clock::now();
    query_res = tlweSymInt32Decrypt<Lvl2>(count_res, std::pow(2.,48), sk.key.get<Lvl2>());
    end = std::chrono::system_clock::now();
    times.aggregation_time = std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count();
    
    std::cout << "Filtering time: " << times.filtering_time << " ms" << std::endl;
    std::cout << "Conversion time: " << times.conversion_time << " ms" << std::endl;
    std::cout << "Aggregation time: " << times.aggregation_time << " ms" << std::endl;
    std::cout << "Total time: " << times.filtering_time + times.conversion_time + times.aggregation_time << " ms" << std::endl;
    std::cout << "Decrypt result: " << query_res << std::endl;
    std::cout << "Plain result: " << plain_result << std::endl;

    std::cout << std::endl;
    std::cout << std::endl;
    std::cout << std::endl;
    std::cout << std::endl;
    
    return times;
}

/**
    SELECT COUNT(*) FROM MobileHealth
    WHERE glucose < 70 OR glucose > 100  AND time > 2023:12:01:00:00
    @param[in] num The size of the database.
*/
QueryTime time_series_query2(size_t num)
{
    QueryTime times;
    std::cout << "Time-Series SQL Query2 Test: "<< std::endl;
    std::cout << "--------------------------------------------------------"<< std::endl;
    std::cout << "Records: " << num << std::endl;
    std::random_device seed_gen;
    std::default_random_engine engine(seed_gen());
    using P = Lvl1;
    TFHESecretKey sk;
    TFHEEvalKey ek;
    using bkP = Lvl01;
    using iksP = Lvl10;
    std::uniform_int_distribution<uint32_t> message(1, P::n-1);
    ek.emplacebkfft<bkP>(sk);
    ek.emplaceiksk<iksP>(sk);
    ek.emplacebkfft<Lvl02>(sk);
    std::vector<uint64_t> glucose(num);
    std::vector<uint64_t> time_values(num);
    uint32_t time_values_width = 7;
    std::vector<TRLWELvl1> glucose_cipher(num);
    std::vector<std::vector<TRLWELvl1>> time_values_cipher(num);

    TRGSWLvl1 predicate1_cipher, predicate2_cipher;
    std::vector<TRGSWLvl1> predicate3_cipher(time_values_width);
    exponent_encrypt_rgsw<P>(70, predicate1_cipher, sk, true);
    exponent_encrypt_rgsw<P>(100, predicate2_cipher, sk, true);
    uint64_t predicate_time_value = 1672502400000;
    exponent_encrypt_rgsw<P>(predicate_time_value, 64, predicate3_cipher, sk, true);
    
    // Start sql evaluation
    std::vector<TLWELvl1> filter_res(num);
    std::vector<TLWELvl2> aggregation_res(num);
    TLWELvl2 count_res;
    
    #pragma omp parallel for num_threads(48)
    for (size_t i = 0; i < num; i++)
    {
        // Generate data
        glucose[i] = i % 2 == 0 ? 80 : message(engine);
        time_values[i] = i % 4 == 0 ? predicate_time_value - i : predicate_time_value + i;
        
        // Encrypt
        exponent_encrypt<P>(glucose[i], glucose_cipher[i], sk);
        time_values_cipher[i].resize(time_values_width);
        exponent_encrypt<P>(time_values[i], 64, time_values_cipher[i], sk);
    }

    std::chrono::system_clock::time_point start, end;
    start = std::chrono::system_clock::now();

    #pragma omp parallel for num_threads(48)
    for (size_t i = 0; i < num; i++)
    {
        
        TLWELvl1 pre_res;
        less_than_tfhepp(glucose_cipher[i], predicate1_cipher, filter_res[i], sk);
        greater_than_tfhepp(glucose_cipher[i], predicate2_cipher, pre_res, sk);
        TFHEpp::HomOR(filter_res[i], filter_res[i], pre_res, ek);
        greater_than_tfhepp(time_values_cipher[i], predicate3_cipher, time_values_width, pre_res, ek, sk);
        lift_and_and(filter_res[i], pre_res, aggregation_res[i], 48, ek, sk);
        
    }
    end = std::chrono::system_clock::now();
    times.filtering_time = std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count();

    count_res = aggregation_res[0];
    for (size_t i = 1; i < num; i++)
    {
        for (size_t j = 0; j <= Lvl2::n; j++)
        {
            count_res[j] += aggregation_res[i][j];
        }

    }

    // Conversion time
    start = std::chrono::system_clock::now();
    // 这里没有实际的转换操作，但为了保持一致性，我们仍然记录时间
    end = std::chrono::system_clock::now();
    times.conversion_time = std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count();

    uint64_t plain_result = 0;
    for (size_t i = 0; i < num; i++)
    {
        bool filter_no_time = false;
        if (glucose[i] < 70 || glucose[i] > 100)
        {
            filter_no_time = true;
        }

        if (filter_no_time && (time_values[i] > predicate_time_value))
        {
            plain_result += 1;
        }

    }
    
    // Aggregation time
    start = std::chrono::system_clock::now();
    uint64_t query_res = tlweSymInt32Decrypt<Lvl2>(count_res, std::pow(2.,48), sk.key.get<Lvl2>());
    end = std::chrono::system_clock::now();
    times.aggregation_time = std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count();

    std::cout << "Filtering time: " << times.filtering_time << " ms" << std::endl;
    std::cout << "Conversion time: " << times.conversion_time << " ms" << std::endl;
    std::cout << "Aggregation time: " << times.aggregation_time << " ms" << std::endl;
    std::cout << "Total time: " << times.filtering_time + times.conversion_time + times.aggregation_time << " ms" << std::endl;
    std::cout << "Decrypt result: " << query_res << std::endl;
    std::cout << "Plain result: " << plain_result << std::endl;

    std::cout << std::endl;
    std::cout << std::endl;
    std::cout << std::endl;
    std::cout << std::endl;
    
    return times;
}

/**
    SELECT COUNT(passenger_count) FROM passengers
    WHERE time = 2021:07:01:00:00 AND VecdorID = 2 AND RatecodeID = 2
    @param[in] num The size of the database.
*/
QueryTime time_series_query3(size_t num)
{
    QueryTime times;
    std::cout << "Time-Series SQL Query3 Test: "<< std::endl;
    std::cout << "--------------------------------------------------------"<< std::endl;
    std::cout << "Records: " << num << std::endl;
    std::random_device seed_gen;
    std::default_random_engine engine(seed_gen());
    using P = Lvl1;
    TFHESecretKey sk;
    TFHEEvalKey ek;
    using bkP = Lvl01;
    using iksP = Lvl10;
    std::uniform_int_distribution<uint32_t> message(1, P::n-1);
    ek.emplacebkfft<bkP>(sk);
    ek.emplaceiksk<iksP>(sk);
    ek.emplacebkfft<Lvl02>(sk);
    std::vector<uint64_t> VecdorID(num);
    std::vector<uint64_t> RatecodeID(num);
    std::vector<uint64_t> time_values(num);
    uint32_t time_values_width = 7;
    std::vector<TRLWELvl1> VecdorID_cipher(num);
    std::vector<TRLWELvl1> RatecodeID_cipher(num);
    std::vector<std::vector<TRLWELvl1>> time_values_cipher(num);

    TRGSWLvl1 predicate1_cipher, predicate2_cipher;
    std::vector<TRGSWLvl1> predicate3_cipher(time_values_width);
    exponent_encrypt_rgsw<P>(2, predicate1_cipher, sk, true);
    exponent_encrypt_rgsw<P>(2, predicate2_cipher, sk, true);
    uint64_t predicate_time_value = 1688140800;
    exponent_encrypt_rgsw<P>(predicate_time_value, 64, predicate3_cipher, sk, true);
    
    // Start sql evaluation
    std::vector<TLWELvl1> filter_res(num);
    std::vector<TLWELvl2> aggregation_res(num);
    TLWELvl2 count_res;
    
    #pragma omp parallel for num_threads(48)
    for (size_t i = 0; i < num; i++)
    {
        // Generate data
        VecdorID[i] = i % 100 == 0 ? 2 : message(engine);
        RatecodeID[i] = i % 100 == 0 ? 2 : message(engine);
        time_values[i] = i % 100 == 0 ? predicate_time_value : predicate_time_value + i;
        
        // Encrypt
        exponent_encrypt<P>(VecdorID[i], VecdorID_cipher[i], sk);
        exponent_encrypt<P>(RatecodeID[i], RatecodeID_cipher[i], sk);
        time_values_cipher[i].resize(time_values_width);
        exponent_encrypt<P>(time_values[i], 64, time_values_cipher[i], sk);
    }

    std::chrono::system_clock::time_point start, end;
    start = std::chrono::system_clock::now();

    #pragma omp parallel for num_threads(48)
    for (size_t i = 0; i < num; i++)
    {
        
        TLWELvl1 pre_res;
        equality_tfhepp(VecdorID_cipher[i], predicate1_cipher, filter_res[i], sk);
        equality_tfhepp(RatecodeID_cipher[i], predicate1_cipher, pre_res, sk);
        TFHEpp::HomAND(filter_res[i], filter_res[i], pre_res, ek);
        equality_tfhepp(time_values_cipher[i], predicate3_cipher, time_values_width, pre_res, ek, sk);
        lift_and_and(filter_res[i], pre_res, aggregation_res[i], 48, ek, sk);
        
    }
    end = std::chrono::system_clock::now();
    times.filtering_time = std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count();

    count_res = aggregation_res[0];
    for (size_t i = 1; i < num; i++)
    {
        for (size_t j = 0; j <= Lvl2::n; j++)
        {
            count_res[j] += aggregation_res[i][j];
        }

    }

    // Conversion time
    start = std::chrono::system_clock::now();
    // 这里没有实际的转换操作，但为了保持一致性，我们仍然记录时间
    end = std::chrono::system_clock::now();
    times.conversion_time = std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count();

    uint64_t plain_result = 0;
    for (size_t i = 0; i < num; i++)
    {
        bool filter_no_time = false;
        if (VecdorID[i] == 2 && RatecodeID[i] == 2)
        {
            filter_no_time = true;
        }

        if (filter_no_time && (time_values[i] == predicate_time_value))
        {
            plain_result += 1;
        }

    }
    
    // Aggregation time
    start = std::chrono::system_clock::now();
    uint64_t query_res = tlweSymInt32Decrypt<Lvl2>(count_res, std::pow(2.,48), sk.key.get<Lvl2>());
    end = std::chrono::system_clock::now();
    times.aggregation_time = std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count();

    std::cout << "Filtering time: " << times.filtering_time << " ms" << std::endl;
    std::cout << "Conversion time: " << times.conversion_time << " ms" << std::endl;
    std::cout << "Aggregation time: " << times.aggregation_time << " ms" << std::endl;
    std::cout << "Total time: " << times.filtering_time + times.conversion_time + times.aggregation_time << " ms" << std::endl;
    std::cout << "Decrypt result: " << query_res << std::endl;
    std::cout << "Plain result: " << plain_result << std::endl;

    std::cout << std::endl;
    std::cout << std::endl;
    std::cout << std::endl;
    std::cout << std::endl;
    
    return times;
}

/**
    SELECT SUM(fare_amount) FROM fare
    WHERE (time BETWEEN 2016:01:01:00:00 AND 2016:01:03:00:00)
    @param[in] num The size of the database.
*/
QueryTime time_series_query4(size_t num)
{
    QueryTime times;
    std::cout << "Time-Series SQL Query4 Test: "<< std::endl;
    std::cout << "--------------------------------------------------------"<< std::endl;
    std::cout << "Records: " << num << std::endl;
    std::random_device seed_gen;
    std::default_random_engine engine(seed_gen());
    using P = Lvl1;
    TFHESecretKey sk;
    TFHEEvalKey ek;
    using bkP = Lvl01;
    using iksP = Lvl10;
    std::uniform_int_distribution<uint32_t> message(1, P::n-1);
    ek.emplacebkfft<bkP>(sk);
    ek.emplaceiksk<iksP>(sk);
    ek.emplacebkfft<Lvl02>(sk);

    // Filtering
    std::vector<uint64_t> time_values(num);

    uint32_t time_values_width = 7;
    std::vector<std::vector<TRLWELvl1>> time_values_cipher(num);

    std::vector<TRGSWLvl1> predicate1_cipher(time_values_width);
    std::vector<TRGSWLvl1> predicate2_cipher(time_values_width);
    uint64_t predicate_time_value1 = 1451577600000, predicate_time_value2 = 1451750400000;
    exponent_encrypt_rgsw<P>(predicate_time_value1, 64, predicate1_cipher, sk, true);
    exponent_encrypt_rgsw<P>(predicate_time_value2, 64, predicate2_cipher, sk, true);

    std::vector<double> fare_amount(num);

    for (size_t i = 0; i < num; i++)
    {
        fare_amount[i] = message(engine);
    }

    // Start sql evaluation
    std::vector<TLWELvl1> filter_res(num);
    std::vector<TLWELvl2> aggregation_res(num);
    TLWELvl2 count_res;
    
    #pragma omp parallel for num_threads(48)
    for (size_t i = 0; i < num; i++)
    {
        // Generate data
        time_values[i] = i % 256 == 0 ? predicate_time_value1 + 100 : predicate_time_value2 + 100;
        
        // Encrypt
        time_values_cipher[i].resize(time_values_width);
        exponent_encrypt<P>(time_values[i], 64, time_values_cipher[i], sk);
    }

    std::chrono::system_clock::time_point start, end;
    start = std::chrono::system_clock::now();

    #pragma omp parallel for num_threads(48)
    for (size_t i = 0; i < num; i++)
    {
        
        TLWELvl1 pre_res;
        greater_than_tfhepp(time_values_cipher[i], predicate1_cipher, time_values_width, filter_res[i], ek, sk);
        less_than_tfhepp(time_values_cipher[i], predicate2_cipher, time_values_width, pre_res, ek, sk);
        lift_and_and(filter_res[i], pre_res, filter_res[i], 29, ek, sk);
        
    }
    end = std::chrono::system_clock::now();
    times.filtering_time = std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count();

    std::vector<uint64_t> plain_filter_res(num);
    uint64_t plain_agg_res = 0;
    for (size_t i = 0; i < num; i++)
    {
        if (time_values[i] > predicate_time_value1 && time_values[i] < predicate_time_value2)
        {
            plain_filter_res[i] = 1.;
            plain_agg_res += fare_amount[i];
        }
        else
        {
            plain_filter_res[i] = 0.;
        }

    }

    std::cout << "Filtering finish" << std::endl;

    std::cout << "Aggregation :" << std::endl;
    uint64_t scale_bits = 29;
    uint64_t modq_bits = 32;
    uint64_t modulus_bits = 45;
    uint64_t repack_scale_bits = modulus_bits + scale_bits - modq_bits;
    uint64_t slots_count = filter_res.size();
    std::cout << "Generating Parameters..." << std::endl;
    seal::EncryptionParameters parms(seal::scheme_type::ckks);
    size_t poly_modulus_degree = 65536;
    parms.set_poly_modulus_degree(poly_modulus_degree);
    parms.set_coeff_modulus(seal::CoeffModulus::Create(poly_modulus_degree, {59, 42, 42, 42, 42, 42, 42, 42, 42, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 59}));
    double scale = std::pow(2.0, scale_bits);

    //context instance
    seal::SEALContext context(parms, true, seal::sec_level_type::none);

    //key generation
    seal::KeyGenerator keygen(context);
    seal::SecretKey seal_secret_key = keygen.secret_key();
    seal::RelinKeys relin_keys;
    keygen.create_relin_keys(relin_keys);
    seal::GaloisKeys galois_keys;
    keygen.create_galois_keys(galois_keys);
    

    //utils
    seal::Encryptor encryptor(context, seal_secret_key);
    seal::Evaluator evaluator(context);
    seal::Decryptor decryptor(context, seal_secret_key);

    //encoder
    seal::CKKSEncoder ckks_encoder(context);

    

    //generate evaluation key
    std::cout << "Generating Conversion Key..." << std::endl;
    LTPreKey pre_key;
    LWEsToRLWEKeyGen(pre_key, std::pow(2., modulus_bits), seal_secret_key, sk, P::n, ckks_encoder, encryptor, context);


    // conversion
    std::cout << "Starting Conversion..." << std::endl;
    seal::Ciphertext result;
    start = std::chrono::system_clock::now();
    LWEsToRLWE(result, filter_res, pre_key, scale, std::pow(2., modq_bits), std::pow(2., modulus_bits - modq_bits), ckks_encoder, galois_keys, relin_keys, evaluator, context);
    HomRound(result, result.scale(), ckks_encoder, relin_keys, evaluator, decryptor, context);
    end = std::chrono::system_clock::now();
    times.conversion_time = std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count();
    seal::Plaintext plain;
    std::vector<double> computed(slots_count);
    decryptor.decrypt(result, plain);
    seal::pack_decode(computed, plain, ckks_encoder);

    double err = 0.;
    
    for (size_t i = 0; i < slots_count; ++i)
    {
        err += std::abs(computed[i] - plain_filter_res[i]);
    }

    printf("Repack average error = %f ~ 2^%.1f\n", err / slots_count, std::log2(err / slots_count));


    // Filter result * data
    seal::Ciphertext fare_amount_cipher;
    double qd = parms.coeff_modulus()[result.coeff_modulus_size() - 1].value();
    seal::pack_encode(fare_amount, qd, plain, ckks_encoder);
    encryptor.encrypt_symmetric(plain, fare_amount_cipher);

    std::cout << "Aggregating price and discount .." << std::endl;
    start = std::chrono::system_clock::now();
    seal::multiply_and_relinearize(result, fare_amount_cipher, result, evaluator, relin_keys);
    evaluator.rescale_to_next_inplace(result);
    std::cout << "Remian modulus: " << result.coeff_modulus_size() << std::endl;
    int logrow = log2(num);
    
    seal::Ciphertext temp;
    for (size_t i = 0; i < logrow; i++)
    {
        temp = result;
        size_t step = 1 << (logrow - i - 1);
        evaluator.rotate_vector_inplace(temp, step, galois_keys);
        evaluator.add_inplace(result, temp);
    }
    end = std::chrono::system_clock::now();
    times.aggregation_time = std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count();
    std::vector<double> agg_result(slots_count);
    decryptor.decrypt(result, plain);
    seal::pack_decode(agg_result, plain, ckks_encoder);

    std::cout << "Plain_result: " << plain_agg_res << std::endl;
    std::cout << "Encrypted query result: " << std::round(agg_result[0]) << std::endl;
    std::cout << "Filtering time: " << times.filtering_time << " ms" << std::endl;
    std::cout << "Conversion time: " << times.conversion_time << " ms" << std::endl;
    std::cout << "Aggregation time: " << times.aggregation_time << " ms" << std::endl;
    std::cout << "Total time: " << times.filtering_time + times.conversion_time + times.aggregation_time << " ms" << std::endl;

    std::cout << std::endl;
    std::cout << std::endl;
    std::cout << std::endl;
    std::cout << std::endl;
    
    return times;
}


int main()
{
    std::vector<QueryTime> times_q1, times_q2, times_q3, times_q4;
    
    // 测试不同规模
    for(int i = 0; i <= 15; i++) {
        size_t num = 1 << i;
        std::cout << "Testing with size 2^" << i << " (" << num << ")" << std::endl;
        
        times_q1.push_back(time_series_query1(num));
        times_q2.push_back(time_series_query2(num));
        times_q3.push_back(time_series_query3(num));
        times_q4.push_back(time_series_query4(num));
    }
    
    // 输出表格头
    std::cout << "\nPerformance Results (time in ms):\n";
    std::cout << std::setw(8) << "Size" << " | "
              << std::setw(12) << "Operation" << " | "
              << std::setw(10) << "Query 1" << " | "
              << std::setw(10) << "Query 2" << " | "
              << std::setw(10) << "Query 3" << " | "
              << std::setw(10) << "Query 4" << std::endl;
    std::cout << std::string(80, '-') << std::endl;
    
    // 输出每个规模的结果
    for(int i = 0; i <= 15; i++) {
        size_t num = 1 << i;
        
        // 输出过滤时间
        std::cout << std::setw(8) << num << " | "
                  << std::setw(12) << "Filtering" << " | "
                  << std::setw(10) << times_q1[i].filtering_time << " | "
                  << std::setw(10) << times_q2[i].filtering_time << " | "
                  << std::setw(10) << times_q3[i].filtering_time << " | "
                  << std::setw(10) << times_q4[i].filtering_time << std::endl;
                  
        // 输出转换时间
        std::cout << std::setw(8) << "" << " | "
                  << std::setw(12) << "Conversion" << " | "
                  << std::setw(10) << times_q1[i].conversion_time << " | "
                  << std::setw(10) << times_q2[i].conversion_time << " | "
                  << std::setw(10) << times_q3[i].conversion_time << " | "
                  << std::setw(10) << times_q4[i].conversion_time << std::endl;
                  
        // 输出聚合时间
        std::cout << std::setw(8) << "" << " | "
                  << std::setw(12) << "Aggregation" << " | "
                  << std::setw(10) << times_q1[i].aggregation_time << " | "
                  << std::setw(10) << times_q2[i].aggregation_time << " | "
                  << std::setw(10) << times_q3[i].aggregation_time << " | "
                  << std::setw(10) << times_q4[i].aggregation_time << std::endl;
                  
        std::cout << std::string(80, '-') << std::endl;
    }
    
    return 0;
}