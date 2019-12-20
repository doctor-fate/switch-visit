cmake_minimum_required(VERSION 3.8)

if (${CMAKE_VERSION} VERSION_LESS 3.13)
    cmake_policy(VERSION ${CMAKE_MAJOR_VERSION}.${CMAKE_MINOR_VERSION})
else ()
    cmake_policy(VERSION 3.13)
endif ()

set(CMAKE_POLICY_DEFAULT_CMP0077 NEW)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

project(switch-visit VERSION 0.9.1)

add_library(switch-visit INTERFACE)
target_sources(switch-visit INTERFACE ${PROJECT_SOURCE_DIR}/Ubiq/SwitchVisit.h)
target_include_directories(switch-visit INTERFACE $<BUILD_INTERFACE:${PROJECT_SOURCE_DIR}>)

add_executable(switch-visit-example main.cpp)
target_link_libraries(switch-visit-example PRIVATE switch-visit)