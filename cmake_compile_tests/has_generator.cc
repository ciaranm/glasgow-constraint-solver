#include <version>
#ifdef __cpp_lib_generator
#include <generator>
#else
#error "need to use external implementation of <generator>"
#endif

int main(int, char *[])
{
    return 0;
}
