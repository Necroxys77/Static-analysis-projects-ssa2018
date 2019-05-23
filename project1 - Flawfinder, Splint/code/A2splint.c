#include <stdio.h>
#include <stdlib.h>

static void stringcopy(/*@out@*/char *str1, char *str2)
/*@requires maxSet(str1)>=15 /\ maxRead(str2)>=0 @*/
/*@ensures maxSet(str1) == 15 @*/;

int main(int argc, char **argv)
/*@requires maxRead(argv) >= 1 /\ maxRead(argv[1])>=0 @*/;

/*@only@*/ /*@null@*/ void *malloc(size_t size);

void free (/*@only@*/ /*@out@*/ /*@null@*/ void *ptr);

static void stringcopy(char *str1, char *str2){
int i = 0;
int max_size = 16;

while (*str2!='\0' && i < max_size -1){
    *str1++ = *str2++;
    i++;
}
str1[max_size-1] = '\0';
}


int main(/*@unused@*/int argc, char **argv)
{
/*@owned@*/ /*@null@*/ char *buffer;
buffer = (char *) malloc(16 * sizeof(char));

if(buffer == NULL)
    return 0;

if(argv[1]!=NULL){
    stringcopy(buffer, argv[1]);
    printf("%s\n", buffer); // Flawfinder: ignore
}


free(buffer);
return 0;

}
