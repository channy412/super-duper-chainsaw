cmake_minimum_required(VERSION 3.10)
project(MathematicalAlgorithm_FFT)

set(CMAKE_CXX_STANDARD 14)

add_executable(MathematicalAlgorithm_FFT main.cpp processing.cpp processing.h simple_wav.cpp simple_wav.h svg_module.cpp svg_module.h)