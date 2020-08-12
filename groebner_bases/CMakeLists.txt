cmake_minimum_required(VERSION 3.10)
project(Grobner_bases)



set(CMAKE_CXX_STANDARD 14)
set(CMAKE_MODULE_PATH "${CMAKE_SOURCE_DIR}")
find_package(GMP REQUIRED)


#set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -lgmp" )
#set (CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -lgmpxx")
#set(CMAKE_CXX_FLAGS "-lgm pxx" )

add_executable(Grobner_bases main.cpp GroebnerBasis.cpp GroebnerBasis.h)


target_link_libraries(Grobner_bases gmp gmpxx)

