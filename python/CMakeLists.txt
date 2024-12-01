include_directories(${CMAKE_SOURCE_DIR}/generator/src/generator/include)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR})

include(FetchContent)
FetchContent_Declare(
        pybind11
        GIT_REPOSITORY https://github.com/pybind/pybind11
        GIT_TAG v2.13.1
)
FetchContent_MakeAvailable(pybind11)

pybind11_add_module(gcspy gcspy.cc)
target_link_libraries(gcspy PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(gcspy LINK_PUBLIC ${Boost_LIBRARIES})
target_link_libraries(gcspy PRIVATE fmt::fmt)

install(TARGETS gcspy DESTINATION .)

configure_file(${CMAKE_SOURCE_DIR}/python/python_test.py ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/python/python_test.py COPYONLY)
#add_test(NAME python_bindings COMMAND ${PYTHON_EXECUTABLE} ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/python/python_test.py)
