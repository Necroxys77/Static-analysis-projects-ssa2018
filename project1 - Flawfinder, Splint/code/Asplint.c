#include <stdio.h>
#include <stdlib.h>

/* command: splint +bounds A.c */

/*@null@*/ static char *stringcopy( /*@partial@*/ char *str1,  /*@returned@*/ char *str2)
/*@requires maxSet(str1)>=15 /\ maxRead(str2)>=0 @*/
/*@ensures maxRead (str2) >= maxRead(str1) /\ maxRead (str1) <= 15@*/;

int main(int argc, char **argv)
/*@requires maxRead(argv) >= 1 /\ maxRead(argv[1])>=0 @*/;


static char *stringcopy(char *str1, char *str2) // static used to handle the fact that this function is not used outside A.c
{
int i = 0;
int max_size = 16;

if(str2 == NULL)
    return NULL;

while (*str2!='\0' && i < max_size - 1){ // -boolops to permit condition on no bool values AND Possible out-of-bounds read: *str2 (safe)
    *str1++ = *str2++;
    i++;
}
str1[max_size-1] = '\0';

return str2; //non serve a niente
}


int main(/*@unused@*/int argc, char **argv) // to handle unused argument
{
/*@owned@*/ /*@null@*/ char *buffer;
buffer = (char *) malloc(16 * sizeof(char));

if(buffer == NULL)
    return 0;

if(argv[1]!=NULL){ // to handle the fact that the buffer may be NULL
    /*@null@*/ char* res; //it generates an other error for not releasing the fresh memory, but I think that this is ok (-mustdefine to disable warning)
    res = stringcopy(buffer, argv[1]); // to handle possible null values in input
    printf("%s\n", buffer); // Flawfinder: ignore
}

free(buffer); //to handle memory leak
return 0; //to handle missing return

}

