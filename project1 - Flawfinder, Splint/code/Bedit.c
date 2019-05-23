#include <stdlib.h>


static ssize_t my_read(int fd, /*@partial@*/void *buf, size_t size)
/*@requires maxSet(buf) >= (size-1)@*/;



static ssize_t my_read(int fd, void *buf, size_t size){
    ssize_t bytesBuf;
    size_t bytesRead=0;
    char *copy;

    copy = buf;
    do {
        bytesBuf = read(fd, copy, (size-bytesRead)); // Flawfinder: ignore
        bytesRead += bytesBuf;
        if(bytesBuf == -1){
            return 0;
        }
        copy += bytesBuf;
    }
    while(bytesBuf != 0);

    return 1;
}


void func(int fd){
    /*@null@*/ char *buf;
    size_t len = 0;
    ssize_t bytesLen, res;

    //len = malloc(sizeof(size_t));
    bytesLen = my_read(fd, &len, sizeof(len));
    if (bytesLen == 0 || len > 1024){
        return;
    }

    buf = malloc(len+1);
    
    if(buf == NULL){
        return;
    }

    res = my_read(fd, buf, len);
    if(res==1){
        buf[len] = '\0';
        free(buf);
    }
    else{
        free(buf);
    }
}
