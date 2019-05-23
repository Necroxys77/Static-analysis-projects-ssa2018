#include <stdlib.h>

/* command:  splint +posixlib +bounds C.c */

static size_t max_value = __SIZE_MAX__; // 2^64-1

void func(int fd){
    /*@null@*/char *buf;
    char *copy;
    size_t len, bytesRead = 0;
    ssize_t bytesLen, bytesBuf;
    
    bytesLen = read(fd, &len, sizeof(len)); // Flawfinder: ignore
    if (bytesLen == -1 || len == max_value)
        return;

    buf = malloc(len+1); 
    
    if(buf == NULL)
        return;

    copy = buf;
    do {
        bytesBuf = read(fd, copy, (len-bytesRead)); // Flawfinder: ignore
        bytesRead += bytesBuf;
        if(bytesBuf == -1){ //|| bytesRead > len
            free(buf);
            return;
        }
        copy += bytesBuf;
    }
    while(bytesBuf != 0);

    buf[len] = '\0';
    free(buf);
}
