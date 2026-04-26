#include <version>
#ifdef __cpp_lib_format
#include <format>
#else
#error "need to use external implementation of <format>"
#endif

#ifdef __cpp_lib_print
#include <print>
#else
#error "need to use external implementation of <print>"
#endif

int main(int, char *[])
{
    return 0;
}
