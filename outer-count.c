
/**
MIT License

Copyright (c) 2022 Martina Seidl

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

**/

// tool for counting 
// 	* assignments of outermost exist. vars that satisfy a QBF \exists ...
//	* assignments of outermost univ. vars that falsify a QBF \forall ....



#include <limits.h>
#include <assert.h>
#include <string.h>
#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>

#include "qdpll.h"


static int *vars, *vals, num_vars, num_cls, qblocks;
static char *line;
static size_t len = 0;  
static ssize_t read = 0;  
static QDPLL *depqbf; 		// instance of DepQBF
static int tseitin_var = 0; 	// definition of the input formula
static int is_true = -1; 	// input formula is true
static int max_var = 0; 	// max var index usedw
static char first = 0; 
static QDPLLResult res; 	// solving result
static Nesting nesting; 	// innermost nesting for adding vars
static int free_vars = 0; 
static int empty_cl = 0; 


// parse the matrix
static char *parse (FILE *ifile) {
  unsigned int i; 
  int tmp; 
  int added = 0; 
  int mult; 
  int sign = 0;
  int cl_size = 0;  
 
  while (read != -1) {
    i = 0; 
    added = 0; 

    while ((i < read) && (line [i] == ' ')) i++; 

    if (i < read -1) qdpll_add (depqbf, -tseitin_var); 

    cl_size = 0; 
    while (i < read-1) {
      tmp = 0; 
      mult = 1; 
      sign = 1; 
      while ((i < read-1) && (line [i] != ' ')) {
	if (line [i] == '-') {
          i++; 
	  sign = -1; 
	}
	if (!isdigit (line [i])) return "unexpected character in clause"; 
        tmp = tmp * mult +  (line [i] - '0');
	i++;
	mult = 10; 
      }


      assert (tmp <= num_vars); 
      if (tmp && !vars [tmp]) { free_vars = 1; }
      qdpll_add (depqbf, sign * tmp); 
      added = 1; 
      if (tmp) cl_size++; 

      while ((i < read) && (line [i] == ' ')) i++; 
    }
    if (!cl_size && added) empty_cl = 1; 
    if (feof (ifile)) break; 
    read = getline (&line, &len, ifile); 
 
  }

  return 0; 
}


//parse the prefix
static char * parse_prefix (FILE * ifile) {
  char q = 'u'; 
  int block = 0; 
  unsigned int i; 
  int tmp; 
  int mult;
  int block_size = 0; 

  do { 
    read = getline (&line, &len, ifile); 
  } while (!feof (ifile) && line [0] == 'c'); 

  if (feof (ifile)) return "header not found in qdimacs file"; 

  if (!sscanf (line, "p cnf %d %d", &num_vars, &num_cls)) 
	 return "invalid header in qdimacs file";  


  printf ("number of vars: %d\n", num_vars); 
  printf ("number of clauses: %d\n", num_cls); 

  tseitin_var = num_vars + 1;
  max_var = tseitin_var + 1; 

  vars = (int *) malloc (sizeof (int) * (num_vars + 1)) ;
  vals = (int *) malloc (sizeof (int) * (num_vars + 1)) ;
  memset (vars, 0, num_vars+1); 
  memset (vals, 0, num_vars+1); 

  read = getline (&line, &len, ifile); 

  while (read && ((line [0] == 'a') || line [0] == 'e')) {
    if (!first) {
	first = line [0];
	printf ("first quantifier: %c\n", first); 
    }	

    if (line [0] != q) {

      if (block) {
        printf ("size of block %d: %d \n", block, block_size); 
	block_size = 0; 
	qdpll_add (depqbf, 0); 
      }
      block++; 
      q = line [0];

      if (line [0] == 'a') qdpll_new_scope (depqbf, QDPLL_QTYPE_FORALL); 
      else nesting = qdpll_new_scope (depqbf, QDPLL_QTYPE_EXISTS); 

    }

    i = 1; 

    while ((i < read) && (line [i] == ' ')) i++; 

    if (i == read) return "invalid quantifier block"; 

    while (i < read-1) {
      tmp = 0; 
      mult = 1; 
      while ((i < read-1) && (line [i] != ' ')) {
	if (!isdigit (line [i])) return "unexpected character in prefix"; 
        tmp = tmp * mult +  (line [i] - '0');
	i++;
	mult = 10; 

      }
      if (tmp) vars [tmp] = block; 
      if (tmp) qdpll_add (depqbf, tmp); 
      if (tmp) block_size++; 

      while ((i < read) && (line [i] == ' ')) i++; 
    } 

    if (feof (ifile)) break; 
    read = getline (&line, &len, ifile); 

  }


  qblocks = block; 
  if (qblocks) qdpll_add (depqbf, 0); 


  if (!nesting) {
       nesting = qdpll_new_scope (depqbf, QDPLL_QTYPE_EXISTS); 
       qdpll_add (depqbf, 0); 
       if (!first) first = 'e'; 
  }

  qdpll_add_var_to_scope (depqbf, tseitin_var, nesting);
  qdpll_add_var_to_scope (depqbf, max_var, nesting);

  return 0;
}




static unsigned long count () {
  unsigned long c = 0;
  unsigned long max_free = ULONG_MAX; 
  unsigned long print_counter = 100, print_step = 100; 
  int dont_cares; 
  int i;
  int pushed = 0; 

  qdpll_assume (depqbf, tseitin_var); 
						// check truth value of formula
  if (qdpll_sat (depqbf) == QDPLL_RESULT_SAT) { 
    is_true = 1; 
    assert ((first == 'e') || free_vars); 
    printf ("the formula is true\n"); 
  } else {
    is_true = 0; 
    assert (first == 'a'); 
    printf ("the formula is false\n"); 
  }

  for (i = 1; i <= num_vars; i++) {
    if (qdpll_is_var_declared(depqbf, i) && (vars [i] <= 1)) {
      printf ("%d ", qdpll_get_value (depqbf, i) * i ); 
    }
  }
  printf ("\n"); 

  do {
    unsigned long d = 1; 
    dont_cares = 0; 
    for (i = 1; i <= num_vars; i++) {
      if ((vars [i] <= 1) && qdpll_is_var_declared (depqbf, i)) {
        vals [i] = qdpll_get_value (depqbf, i);
	if (vals [i] == QDPLL_ASSIGNMENT_UNDEF) {
		d = d*2; 
		dont_cares++; 
	}
      }
    }

    if (dont_cares) printf ("%d variables were unassigned in partial (counter-)model\n", dont_cares); 

    if (dont_cares >= 64) {
	printf ("more than 2^64 (counter-)models found - counting stopped\n"); 
	return ULONG_MAX; 
    }


    qdpll_reset (depqbf); 
    if (pushed) {
	    qdpll_pop (depqbf); 
	    pushed = 0; 
    }
   
    if (max_free < d) {
      printf ("overflow with %lu + %lu (counter-)models\n", c, d); 
      return ULONG_MAX; 
    }

    c = c + d; 
    max_free -= d; 

    if (c < 100) {
      printf ("current count: %lu\n", c); 
    } else {

      if (c >= print_counter) {
        printf ("current count: %lu\n", c); 
        print_counter += print_step; 
	if (c > 10000) print_step = 500; 
	if (c > 100000) print_step = 1000; 	
      }
    }


    fflush (stdout); 

    for (i = 1; i <= num_vars; i++) {
      if (vars [i] <= 1) {
	if (vals [i] == QDPLL_ASSIGNMENT_UNDEF) continue; 
	if (is_true) {
          qdpll_add (depqbf, -i*vals[i]); 
	} else {
          qdpll_add (depqbf, -max_var); 
          qdpll_add (depqbf, i*vals[i]); 
          qdpll_add (depqbf, 0); 
	}
      }
    }

    if (is_true) {
      qdpll_add (depqbf, 0); 
      qdpll_assume (depqbf, tseitin_var); 
    } else {
      qdpll_push (depqbf); 
      pushed = 1; 
      for (i = num_vars + 1; i <= max_var; i++) {
        qdpll_add (depqbf, i);
      }
      qdpll_add (depqbf, 0); 
      max_var++;
      if (nesting) qdpll_add_var_to_scope (depqbf, max_var, nesting);
    }
    res = qdpll_sat (depqbf); 
  } while 
    ((is_true && (res == QDPLL_RESULT_SAT))  ||
    (!is_true && (res == QDPLL_RESULT_UNSAT)) );


  return c; 
}


int main (int argc, char **argv) {
  FILE *qdimacsFile; // file with QBF
  char *err; 	     // error message

  if (argc != 2) {
    fprintf (stderr, "invalid number of arguments\n"); 
    fprintf (stderr, "usage: outer-count <qdimacs-file>\n"); 
    return -1; 
  }

  qdimacsFile = fopen (argv [1], "r"); 

  if (!qdimacsFile) {
    fprintf (stderr, "cannot read qdimacs file\n"); 
    fprintf (stderr, "usage: outer-count <qdimacs-file>\n"); 
    return -1; 
  }

  depqbf = qdpll_create (); 

  // use depqbf in incremental mode
  qdpll_configure (depqbf, "--no-dynamic-nenofex"); 
  qdpll_configure (depqbf, "--incremental-use"); 
  qdpll_configure (depqbf, "--dep-man=simple"); 

  // parse prefix
  err =  parse_prefix (qdimacsFile); 

  if (err) {
    fprintf (stderr, "%s\n", err); 
    free (line); 
    return -1; 
  }
  
  // parse matrix
  err =  parse (qdimacsFile); 

  printf ("%d %d\n", num_cls, empty_cl); 
  if (!num_cls || empty_cl) {
    fprintf (stderr, "%s\n", "formula is empty or contains empty clause"); 
    free (line); 
    free (vars); 
    free (vals); 
    fclose (qdimacsFile); 
    return 0; 
  }


  // start counting
  unsigned long c = count ();

  if (c == ULONG_MAX) 
    printf ("there are > %lu solutions for the outermost vars\n", ULONG_MAX);
  else
    printf ("there are %lu solutions for the outermost vars\n", c);  

  qdpll_delete (depqbf); 
  free (line); 
  free (vars); 
  free (vals); 
  fclose (qdimacsFile); 

  fflush (stdout); 
  return 0; 

}
