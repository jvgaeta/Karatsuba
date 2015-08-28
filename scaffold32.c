#include <stdio.h>
#include <stdarg.h>
#include <stdlib.h>
#include <gmp.h>
#include <time.h>
#include <string.h>
#include <unistd.h>
#include "scaffold32.h"

/* You are suppose to change the routine Product32 here to your own routine
 * The mpz calls in the scaffolded Product32 below are the normal GMP function
 * calls and should be neglected. By casting the void pointers as normal unsigned
 * integers, you should be able to access the data values as normal 4 bytes words.
 */

#define max(x, y) (((x) > (y)) ? (x) : (y))
// this is an update via git
 void GradeSchool32(unsigned int *int_a, unsigned int *int_b, unsigned int *int_c, unsigned int wa, unsigned int wb, unsigned int *wc){

    int i, j;
	*wc = wa + wb;

    for (i = 0; i < wa; i++) {
        unsigned int carry = 0;
        for (j = 0; j < wb; j++) {
            unsigned long long int product = (unsigned long long int)int_a[i] * int_b[j] + int_c[i + j] + carry;
            int_c[i + j] = (unsigned int)(product & (0xffffffff));
            carry = (unsigned int)(product >> 32);
        }
        int_c[i + wb] = carry;
    }
}

void addition32(unsigned int *int_a, unsigned int *int_b, unsigned int *int_c, unsigned int wa, unsigned int wb, unsigned int *wc){

	unsigned int c = 0;
	unsigned long long int sum;
	unsigned int *temp;
	int i;
	// here we need to make sure that wa is treated as larger word so swap wa and wb if necessary
	if (wb > wa) {
		temp = int_a;
		int_a = int_b;
		int_b = temp;
		*temp = wa;
		wa = wb;
		wb = *temp;
	}

	for (i = 0; i < wa; i++) {
        if (i < wb) {
            sum = (unsigned long long int)int_a[i] + int_b[i] + c;
        }
        else {
            sum = (unsigned long long int)int_a[i] + c;
        }
        int_c[i] = (unsigned int)(sum & (0xffffffff));
        c = (unsigned int)((sum >> 32) & (0xffffffff));
	}

	while (c > 0) {
		sum = (unsigned long long int)c;
		int_c[i] = (unsigned int)(sum & (0xffffffff));
		c = (unsigned int)((sum >> 32) & (0xffffffff));
		i++;
	}

	*wc = i;

}

void subtraction32(unsigned int *int_a, unsigned int *int_b, unsigned int *int_c, unsigned int wa, unsigned int wb, unsigned int *wc) {
	int i;
	unsigned int c = 0;

	for (i = 0; i < wa; i++) {
		if (int_a[i] < int_b[i]) {
			int_c[i] = int_a[i] - int_b[i] + 4294967296llu;
			int_a[i + 1]--;
		}
		else {
			int_c[i] = int_a[i] - int_b[i];
		}
	}

	*wc = wa;
}


void FastMultiply(unsigned int *int_a, unsigned int *int_b, unsigned int *int_c, unsigned int wa, unsigned int wb, unsigned int *wc) {
	unsigned int wt1, wt2, wtemp2, ww1, ww2, ww3, ww4, wtemp, halved, part, *carry;

	if (wa > wb) {
		halved = wb / 2;
	}
	else {
		halved = wa / 2;
	}
	
	
	part = halved * 2;
	unsigned int *u1 = (unsigned int *)int_a + halved; // lower and upper halves
	unsigned int *u2 = (unsigned int *)int_a;
	unsigned int wu1 = wa - halved;
	unsigned int wu2 = halved;

	unsigned int *v1 = (unsigned int *)int_b + halved; // lower and upper halves
	unsigned int *v2 = (unsigned int *)int_b;
	unsigned int wv1 = wb - halved;
	unsigned int wv2 = halved;
	
	int first_addition_length = max(wu1, wu2) + 2;
	
	
	int second_addition_length = max(wv1, wv2) + 2;
	
	int first_mult_length = first_addition_length + second_addition_length;
	
	int second_mult_length = wu1 + wv1;
	
	int pre_subtraction_length = max(wu1 + wv1, wu2 + wv2) + 2;
	
	int subtraction_length = max(first_addition_length + second_addition_length, pre_subtraction_length);
	
	int max_length = first_addition_length + second_addition_length + first_mult_length + second_mult_length + pre_subtraction_length + subtraction_length;

	unsigned int *mem_pool = (unsigned int *)calloc(max_length, sizeof(unsigned int)); // allocate large block of memory to avoid expensive dynamic allocation

	unsigned int *t1 = &mem_pool[0];
	unsigned int *t2 = &mem_pool[0 + first_addition_length];
	addition32(u1, u2, t1, wu1, wu2, &wt1);

	addition32(v1, v2, t2, wv1, wv2, &wt2);
        

	unsigned int *w3 = &mem_pool[0 + first_addition_length + second_addition_length]; // steps 3,4,5 using recursion
	decision(t1, t2, w3, wt1, wt2, &ww3);
     
	
	unsigned int *w2 = &mem_pool[0 + first_addition_length + second_addition_length + first_mult_length];
	decision(u1, v1, w2, wu1, wv1, &ww2);

	unsigned int *w4 = int_c;
	decision(u2, v2, w4, wu2, wv2, &ww4);
	
	carry  = w4 + halved; // compute carry
        
	
	unsigned int *temp = &mem_pool[0 + first_addition_length + second_addition_length + first_mult_length + second_mult_length];
	
	addition32(w2, w4, temp, ww2, ww4, &wtemp);
	
	unsigned int *temp2 = &mem_pool[0 + first_addition_length + second_addition_length + first_mult_length + second_mult_length + pre_subtraction_length];
	
	if (ww3 >= wtemp) {
		subtraction32(w3, temp, temp2, ww3, wtemp, &wtemp2);
	}
	else {
		subtraction32(temp, w3, temp2, wtemp, ww3, &wtemp2);
	}
	// store updated value where it should be
	w3 = temp2;
	ww3 = wtemp2;

	addition32(w3, carry, int_c + halved, ww3, (ww4 - halved), &ww3); // add the carry and mod w4

	addition32(w2, int_c + part, int_c + part, ww2, (ww3 - halved), &ww2); // add w2 into upper part and mod w3


	free(mem_pool);
	
    	*wc = ww2 + part; // ww2 actually being modded here but it is not visible after simplification



}

int decision(unsigned int *int_a, unsigned int *int_b, unsigned int *int_c, unsigned int wa, unsigned int wb, unsigned int *wc) {
	// this decides whether to use grade school or fast multiply
	if (wa == 0 || wb == 0) {
		*wc = 0;
	}
	else if (wa < 22 || wb < 22 || (wa < wb / 12) || (wb < wa / 12)) {
		GradeSchool32(int_a, int_b, int_c, wa, wb, wc);
	}
	else {
		FastMultiply(int_a, int_b, int_c, wa, wb, wc);
	}
}


/* wa is word length of a, ba is bit length of a */
void Product32(void *a, void *b, void *c, unsigned int wa,
        unsigned int ba, unsigned int wb, unsigned int bb, unsigned int
        *wc, unsigned int *bc){

    /* Cast a and b into short integers of size 32 bits */
    unsigned int *int_a = (unsigned int *) a;
    unsigned int *int_b = (unsigned int *) b;
    unsigned int *int_c = (unsigned int *) c;
    int i;
    for (i = 0; i < wa + wb; i++) {
	int_c[i] = 0;
    }
	//GradeSchool32(int_a, int_b, int_c, wa, wb, wc);
	decision(int_a, int_b, int_c, wa, wb, wc);
}

