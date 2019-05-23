/* MATTEO MARIANI 1815188 
    
    -> this is the safer version of NewBagMatteoMariani.java class.
    See section "Conclusions and Reflections" for further details.

*/

final class Bag {

    /*@ non_null @*/ private int[] contents;
    private int n;
    /*@ invariant 0 <= n; @*/
    /*@ invariant n <= contents.length; @*/

    /*@ ensures n == n_input; @*/
    /*@ ensures input.length == contents.length; @*/
    /*@ requires 0 <= n_input; @*/
    /*@ requires n_input <= input.length; @*/
    Bag( /*@ non_null */ int[] input, int n_input) {
        if(input != null){
            n = n_input;
            contents = new int[input.length];
            arraycopy(input, 0, contents, 0, n);
        } else {
            contents = new int[0];
            n = 0;
        }
    }

    Bag() {
        n = 0;
        contents = new int[0];
    }

    /* the next method should remove only the first occurrence of elt */
    final void deleteFirst(int elt) {
        if (contents != null && n >= 0 && n <= contents.length){
            int[] new_contents;
            //@ loop_invariant (i <= n);
            for (int i = 0; i < n; i++) {
                if (contents[i] == elt) {
                    n--;
                    new_contents = new int[contents.length];
                    arraycopy(contents, 0, new_contents, 0, i);
                    arraycopy(contents, i+1, new_contents, i, n-i);
                    contents = new_contents;
                    return;
                }
            }
        }
    }

    /* the next method should remove from the array *all* the occurrences of elt */
    /*@ ensures (\forall int j; j >= 0 && j < n; contents[j] != elt); @*/
    final void deleteAll(int elt) {
        if (contents != null && n >= 0 && n <= contents.length){
            int n_old = n;
            //@ loop_invariant (i <= n+1);
            for (int i = 0; i < n; i++) {  
                if (contents[i] == elt ) {
                    if (n == 1){
                        n--;
                        contents = new int[contents.length];
                        return;
                    } else {
                        n--;
                        contents[i] = contents[n];
                        i--;
                    }
                }
            }
            if (n_old != n) {
                int[] new_contents = new int[contents.length];
                arraycopy(new_contents, 0, contents, 0, n);
                contents = new_contents;
            }
        }
    }

    /*@ ensures \result >= 0; @*/
    final int getCount(int elt) {
        if (contents == null || n > contents.length)
            return -1;
        int count = 0;
        //@ loop_invariant (i <= n);
        //@ loop_invariant count >= 0;
        for (int i = 0; i < n; i++)
            if (contents[i] == elt) 
                count++; 
        return count;
    }

    /* Warning: you may have a hard time checking the method "add" below.
    ESC/Java2 may warn about a very subtle bug not easy to spot. 
    */ 
    /*@ ensures n == \old(n)+1; @*/
    /*@ ensures contents[\old(n)] == elt; @*/
    final void add(int elt) {
        if (contents == null)
            return;
        if (n == contents.length) {
            int[] new_contents = new int[2*n+1];
            //@ assert n < new_contents.length;
            arraycopy(contents, 0, new_contents, 0, n);
            contents = new_contents;
        }
        if (n < 0 || n >= contents.length) 
            return;
        contents[n]=elt;
        n++;
    }

    /*@ ensures n == contents.length; @*/
    final void add(/*@ non_null @*/ Bag b) {
        if (b != null && contents != null){
            int b_n = b.getN();
            int[] b_contents = b.getContents();
            //@ assume b_n >= 0;
            //@ assume b_n <= b_contents.length;
            //@ assume b_contents != null;
            int size = n + b_n;
            //@ assert size >= 0;
            if (size < 0)
                return;
            int[] new_contents = new int[size];
            arraycopy(this.contents, 0, new_contents, 0, n);
            arraycopy(b_contents, 0, new_contents, n, b_n);
            contents = new_contents;
            n = this.n + b_n;
        }
    }

    /*@ requires 0 <= n_a; @*/
    /*@ requires n_a <= a.length; @*/
    final void add(/*@ non_null @*/ int[] a, int n_a) {
        this.add(new Bag(a,n_a));
    }

    Bag(/*@ non_null @*/ Bag b) {
        n = 0;
        contents = new int[0];
        this.add(b);    
    }


    /*@ requires srcOff >= 0; @*/
    /*@ requires srcOff + length <= src.length; @*/
    /*@ requires destOff >= 0; @*/
    /*@ requires destOff + length <= dest.length; @*/
    /*@ requires length >= 0; @*/
    /*@ assignable dest[*]; @*/
    /*@ ensures (\forall int m; m >= 0 && m < length; dest[destOff+m] == src[srcOff+m]);@*/
    private static void arraycopy(/*@ non_null @*/ int[] src,
                                                   int   srcOff,
                                  /*@ non_null @*/ int[] dest,
                                                   int   destOff,
                                                   int   length) {
        if (src == null || dest == null)
            return;
        if (srcOff < 0 || destOff < 0 || srcOff+length > src.length || destOff+length > dest.length)
            return;
        //@ loop_invariant (i <= length);
        for( int i=0 ; i<length; i++) {
            dest[destOff+i] = src[srcOff+i];
        }
    }


    int getN(){
        return this.n;
    }

    int[] getContents(){
        if (contents == null)
            return null;
        int[] copied_contents = new int[contents.length];
        arraycopy(contents, 0, copied_contents, 0, contents.length);
        //@ assert copied_contents.length == contents.length;
        return copied_contents;
    }



}