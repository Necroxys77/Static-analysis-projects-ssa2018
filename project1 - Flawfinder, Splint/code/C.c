
#include <stdlib.h>
void func(int fd)
{
char *buf;
size_t len;
read(fd, &len, sizeof(len));
buf = malloc(len+1); 
read(fd, buf, len); 
buf[len] = '\0';
}
