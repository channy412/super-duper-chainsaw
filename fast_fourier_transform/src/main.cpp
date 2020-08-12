#include <iostream>
#include <math.h>
#include <complex.h>
#include <cassert>
#include <stdio.h>
#include <complex>
#include <cmath>
#include <vector>

#include "simple_wav.h"
#include "svg_module.h"
#include "processing.h"


std::complex<double> get_nth_root_of_unity(long n, long j) {
    const double PI = M_PI;
    std::complex<double> w = cos(2 * PI * j / (double) n) + sin(2 * PI * j / (double) n) * I;
    return w;
}


std::complex<double> *get_array_of_nth_root_of_unity(long n) {
    if (n >= 0) {
        // for FFT
        auto *arr = new std::complex<double>[n];
        for (int i = 0; i < n; i++) {
            arr[i] = get_nth_root_of_unity(n, i);
        }
        return arr;
    } else {
        // for inverse of FFT
        n = -1 * n;
        auto *arr = new std::complex<double>[n];
        for (int i = 0; i < n; i++) {
            arr[i] = get_nth_root_of_unity(n, -i);
        }
        return arr;
    }
}


// this is the general method ( for FFT and inverse FFT )
template<class T>
std::complex<T> *FFT(std::complex<T> *arr, long n, std::complex<double> *w_array, long count) {
    // make sure n is a power of 2
    if (n == 1) {
        auto *arr_small = new std::complex<T>[1];
        arr_small[0] = arr[0];
        return arr_small;
    }

    // initialize
    auto *r0 = new std::complex<T>[n / 2];
    auto *r1 = new std::complex<T>[n / 2];
    for (int i = 0; i < n / 2; i++) {
        r0[i] = 0;
        r1[i] = 0;
    }

    // get r0 ,r1
    for (int i = 0; i < n / 2; i++) {
        r0[i] = arr[i] + arr[n / 2 + i];
        r1[i] = (arr[i] - arr[n / 2 + i]) * w_array[i * count];
    }

    // recursive call
    std::complex<T> *arr1 = FFT(r0, n / 2, w_array, count * 2); // w * w
    std::complex<T> *arr2 = FFT(r1, n / 2, w_array, count * 2); //  w * w

    // merge
    auto *result = new std::complex<T>[n];
    for (int i = 0; i < n; i++) {
        if (i % 2 == 0)
            result[i] = arr1[i / 2];
        else
            result[i] = arr2[i / 2];
    }

    delete[](r0);
    delete[](r1);
    return result;
}


template<class T>
std::complex<T> *FFT(std::complex<T> *arr, long n) {

    int extended_n = (int) round(pow(2, ceil(log2(n))));
//    assert((extended_n) % 2 == 0);

//    if n is not power of 2, extend input array with zeros
    if (n != extended_n) {
        auto *arr_new = new std::complex<T>[extended_n];
        for (long i = 0; i < extended_n; i++) {
            if (i < n) arr_new[i] = arr[i];
            else arr_new[i] = 0;
        }
        arr = arr_new;
        n = extended_n;
    }

    std::complex<double> *w_array = get_array_of_nth_root_of_unity(n);
    return FFT(arr, n, w_array, 1);
}

template<class T>
std::complex<T> *FFT_inv(std::complex<T> *arr, long n) {
    // make sure n is power of 2
    std::complex<double> *w_array = get_array_of_nth_root_of_unity(-n);
    std::complex<T> *result = FFT(arr, n, w_array, 1);
    for (int i = 0; i < n; i++) {
        result[i] = result[i] / (double) n;
    }
    return result;
}


template<class T>
std::complex<T> *FFT(std::complex<T> *arr, long n, long extended_n) {

    if (n != extended_n) {
        auto *arr_new = new std::complex<T>[extended_n];
        for (long i = 0; i < extended_n; i++) {
            if (i < n) arr_new[i] = arr[i];
            else arr_new[i] = 0;
        }
        arr = arr_new;
        n = extended_n;
    }

    std::complex<double> *w_array = get_array_of_nth_root_of_unity(n);
    return FFT(arr, n, w_array, 1);
}


struct compressed_file {
    short *arr;
    double max_abs;
    long arr_len;
    long original_len;
};


compressed_file run_length_compress(std::complex<double> *arr, long n, int cut_off_threshold) {
    // it is enough to keep the first half ( except for the first element )
    // so number of elements: floor(n/2) + 1    ->   index: 0 to floor(n/2) inclusively

    long length_before_run_length = 2 * (n / 2 + 1);
    auto *pre_compressed_arr = new short[length_before_run_length];

    // first, let's find max to normalize
    double max_abs = 0;
    for (long i = 0; i <= n / 2; i++) {
        if (max_abs < abs(arr[i].real())) max_abs = abs(arr[i].real());
        if (max_abs < abs(arr[i].imag())) max_abs = abs(arr[i].imag());
    }

    for (long i = 0; i <= n / 2; i++) {
        // note that short integer's  MAX is 32767
        // rounding is better because type casting merely cut off fractional part
        pre_compressed_arr[2 * i] = short(round(arr[i].real() * 32767 / max_abs)); // real part
        pre_compressed_arr[2 * i + 1] = short(round(arr[i].imag() * 32767 / max_abs)); // imag part
    }


    // cut off small values
    for (long i = 0; i < length_before_run_length; ++i) {
        if (abs(pre_compressed_arr[i]) < cut_off_threshold) pre_compressed_arr[i] = 0;
    }


    // find our final array size
    long length_non_zero = 0;
    long length_zero = 0;

    if (pre_compressed_arr[0] != 0) length_non_zero++;
    else length_zero++;

    for (long i = 1; i < length_before_run_length; ++i) {
        if (pre_compressed_arr[i] != 0) length_non_zero++;
        else if (pre_compressed_arr[i - 1] != 0) length_zero++; // first zero
    }


    // format: save 0 and save count at next  ( 0 is a flag saying the next number is count_zero)
    long length = length_non_zero + length_zero * 2;
    auto *result = new short[length];

    long k = -1;
    for (long i = 0; i < length_before_run_length; ++i) {
        if (pre_compressed_arr[i] != 0) result[++k] = pre_compressed_arr[i];
        else if (pre_compressed_arr[i - 1] != 0) {
            // first zero
            result[++k] = 0;
            result[++k] = 1;
        } else {
            result[k]++;
            // not first zero
        }
    }

    compressed_file file;
    file.arr = result;
    file.arr_len = length;
    file.original_len = n;
    file.max_abs = max_abs;


    delete[](pre_compressed_arr);
    return file;
}


std::complex<double> *run_length_decompress(compressed_file file) {
    long arr_len = file.arr_len;
    short *arr = file.arr;
    double max_abs = file.max_abs;

    long length_before_run_length = 2 * (file.original_len / 2 + 1);
    auto *pre_compressed_arr = new short[length_before_run_length];

    long k = 0;
    for (long i = 0; i < arr_len; i++) {
        if (arr[i] != 0) pre_compressed_arr[k++] = arr[i];
        else {
            for (int j = 0;
                 j < arr[i + 1]; j++) {  // debug memo : arr[++i] is wrong : since i is always increased when it checks
                pre_compressed_arr[k++] = 0;
            }
            i++;
        }
    }

    auto *result = new std::complex<double>[file.original_len];

    result[0].real(pre_compressed_arr[0] * max_abs / 32767);
    result[0].imag(pre_compressed_arr[1] * max_abs / 32767);

    for (long i = 2; i < length_before_run_length; i = i + 2) {
        result[i / 2].real(pre_compressed_arr[i] * max_abs / 32767);
        result[i / 2].imag(pre_compressed_arr[i + 1] * max_abs / 32767);

        // conjugate
        result[file.original_len - i / 2].real(pre_compressed_arr[i] * max_abs / 32767);
        result[file.original_len - i / 2].imag(-pre_compressed_arr[i + 1] * max_abs / 32767);
    }

    delete[](pre_compressed_arr);
//    delete[](file.arr);
    return result;
}


// wrapper function of run_length_compress
compressed_file lossy_compress(short *arr, long n, int cut_off_threshold) {
    long N_power_of_2 = return_common_larger_size(n, n);
    // now fft this and execute run_len_compress

    complex<double> *f1 = extend_signal(arr, n, N_power_of_2);

    std::complex<double> *fft_ed = FFT(f1, n, N_power_of_2);

    return run_length_compress(fft_ed, N_power_of_2, cut_off_threshold);
}


int main() {

    // define two signals
    short int *buffer1, *buffer2;
    int N1, N2, N_common;

    buffer1 = read_channel1_into_buffer("resample.wav", N1);
    buffer2 = read_channel1_into_buffer("Large Long Echo Hall.wav", N2);

    N_common = return_common_larger_size(N1, N2);
    complex<double> *f1 = extend_signal(buffer1, N1, N_common);
    complex<double> *f2 = extend_signal(buffer2, N2, N_common);


    // plot two signals
    plot_signal(f1, N1, 10, "signal1.svg");
    plot_signal(f2, N2, 10, "signal2.svg");


    // perform convolution of these signals
    complex<double> *f1_fft_ed = FFT(f1, N_common);
    complex<double> *f2_fft_ed = FFT(f2, N_common);

    auto *result_fft_ed = new std::complex<double>[N_common];

    for (long i = 0; i < N_common; i++) {
        // fat dot product
        result_fft_ed[i] = f1_fft_ed[i] * f2_fft_ed[i];
    }
    complex<double> *result = FFT_inv(result_fft_ed, N_common);



    // plot output signal and save sound file
    plot_signal(result, N2, (double) 4 / N_common, "signal_result.svg");
    save_as_wav(result, N_common, (double) 1 / N_common, "audio_convolution.wav");


    // compress the first file
    compressed_file file1 = lossy_compress(buffer1, N1, 3000);


    // uncompress the above file and save restored sound file
    std::complex<double> *f1_fft_restored = run_length_decompress(file1);
    std::complex<double> *signal1_restored = FFT_inv(f1_fft_restored, return_common_larger_size(N1, N1));
    save_as_wav(signal1_restored, N1, 1, "signal1_restored.wav");


    // see compression rate
    std::cout << "compression rate: " << (double) (file1.arr_len * 2 + 24) / (N1 * 2) << std::endl;

    return 0;

}