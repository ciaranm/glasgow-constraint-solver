#include <version>
#ifdef __cpp_lib_stacktrace
#include <stacktrace>
#else
#error "need to use external implementation of <stacktrace>"
#endif

int main(int, char *[])
{
    return 0;
}
