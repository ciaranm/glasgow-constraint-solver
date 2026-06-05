# glasgow_scp_solver: a standalone client that solves a problem given as a
# `.scp` (s-expression CP) file (workflow 3). Reads the model with read_scp from
# the core library; the .scp is the input rather than a --prove by-product.
add_executable(glasgow_scp_solver glasgow_scp_solver.cc)
target_link_libraries(glasgow_scp_solver PRIVATE glasgow_constraint_solver)
target_link_libraries(glasgow_scp_solver PRIVATE cxxopts)
target_link_libraries(glasgow_scp_solver PRIVATE gcs_fmt)
