set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR})
add_executable(xcsp_glasgow_constraint_solver xcsp_glasgow_constraint_solver.cc)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})

find_package(LibXml2 REQUIRED)
include_directories(${LIBXML2_INCLUDE_DIR})

target_link_libraries(xcsp_glasgow_constraint_solver
    PUBLIC
    ${CMAKE_SOURCE_DIR}/xcsp/XCSP3-CPP-Parser/lib/libxcsp3parser.a
    glasgow_constraint_solver
    ${Boost_LIBRARIES}
    ${LIBXML2_LIBRARIES})

include_directories(XCSP3-CPP-Parser/include/)
