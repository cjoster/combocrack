#ifndef COMBOCRACK_C
#define COMBOCRACK_C

/******************************* COPYRIGHT *******************************/
/*                                                                       */
/* This program is not copyrighted. You can do fuck-all you want with    */
/* it.                                                                   */
/*                                                                       */
/* This program is provided with no warranty, either express or implied. */
/*                                                                       */
/*       YOU ASSUME ALL RISK ASSOCIATED WITH USE OF THIS SOFTWARE        */
/*                                                                       */
/* Combination generation code shamelessly stolen from:                  */
/*     http://www.geeksforgeeks.org/                                     */
/*                                                                       */
/*************************************************************************/

/***************************** DOCUMENTATION *****************************/
/*                                                                       */
/* crackcomb.c:                                                          */
/*                                                                       */
/* Author: /u/lordvadr                                                   */
/*                                                                       */
/* This program starts by generating all possible combination of unique  */
/* passwords to a "Keysafe" style combination lock. It then builds a     */
/* directed acyclic graph (DAG) with the combinations. Following that,   */
/* it either will output the DAG in a format suitable to hand to         */
/* GraphVIZ (DOT format) or will brute-force and output the optimal      */
/* sequences of button presses to defeat the lock in the fewest number   */
/* of steps.                                                             */
/*                                                                       */
/* Using the DAG approach, it's easy to see that the absolute lower      */
/* bound for the minimum number of sequences is the width of the         */
/* DAG at its widest point. It is therefor provable that the lower       */
/* bound is:                                                             */
/*                                                                       */
/*               n!                                  n!                  */
/*          ------------        and       -----------------------        */
/*           ((n/2)!)^2                    ((n+1)/2)!*((n-1)/2)!         */
/*                                                                       */
/*   for an even number of buttons       for an odd number of buttons    */
/*                                                                       */
/* ...for a solution. This program finds one of those solutions.         */
/*                                                                       */
/* The program uses alphabetical characters instead of numeric buttons   */
/* so that hypothetical locks with more than 10 buttons can be cracked,  */
/* however the search algorithm becomes VERY slow past about 12 buttons. */
/*                                                                       */
/* Use the `tr` program to translate the output back to numeric (see     */
/* below) if so desired.                                                 */
/*                                                                       */
/* The author makes no suggestion that this is the most efficient way    */
/* to brute-force a full-mesh directed acyclic graph, only that this     */
/* program produces the optimal button sequence in as few seq sequences  */
/* as possible.                                                          */
/*                                                                       */
/*  *** *** *** *** *** *** *** *** *** *** *** *** *** *** *** *** ***  */
/*                                                                       */
/* compile with:                                                         */
/*                                                                       */
/*     gcc -Wall -O3 -o combocrack combocrack.c                          */
/*                                                                       */
/* Getting started:                                                      */
/*                                                                       */
/*     ./combocrack -h                                                   */
/*                                                                       */
/*  *** *** *** *** *** *** *** *** *** *** *** *** *** *** *** *** ***  */
/*                                                                       */
/* Examples:                                                             */
/*                                                                       */
/*   Output optimal search sequence for n=10:                            */
/*                                                                       */
/*     ./combocrack -n 10                                                */
/*                                                                       */
/*   Output optimal search sequence for n=10 in numeric form:            */
/*                                                                       */
/*     ./combocrack -n 10 | tr 'ABCDEFGHIJ' '1234567890'                 */
/*                                                                       */
/*   Output optimal search sequence for n=10 but only 3-5 length         */
/*   combinations:                                                       */
/*                                                                       */
/*     ./combocrack -n 10 -m 3 -x 5                                      */
/*                                                                       */
/*   Dump the DAG for n=5:                                               */
/*                                                                       */
/*     ./combocrack -n 5 -d                                              */
/*                                                                       */
/*   Generate PNG for DAG of length 4:                                   */
/*                                                                       */
/*     ./combocrack -n 4 -d | dot -Tpng -o                               */
/*                                                                       */
/*************************************************************************/

/*************************************************************************/
/******************************** DEFINES ********************************/
/*************************************************************************/

#define PROGNAME "combocrack"
#define DEF_NBUTTONS 4
#define DEF_MIN_LEN 1

/*************************************************************************/
/******************************* INCLUDES ********************************/
/*************************************************************************/

#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>
#include <sys/types.h>
#include <time.h>
#include <stdarg.h>
#include <string.h>

/*************************************************************************/
/********************************* TYPES *********************************/
/*************************************************************************/

/* Since we artificially limit the algorithm to 27, name and next are
 * statically allocated. This does waste a little bit of memory, but
 * the malloc/realloc/free time is significant when the graph grows
 * large. Size 32 was chosen for alignment, although I never cared to
 * check if that was correct                                             */
typedef struct comb {
    char name[32];               /* Combination                          */
    unsigned int valid;          /* Is it valid                          */
    unsigned int visited;        /* Has the node been visited yet        */
    unsigned int num_children;   /* Number of children below us          */
    unsigned long last_seq;      /* Last sequence we were counted in     */
    unsigned int last_count;     /* Last count to keep track of          */   
    struct comb *next[32];       /* Next nodes in the tree               */
} comb_t;

/*************************************************************************/
/******************************** GLOBALS ********************************/
/*************************************************************************/

/* Run-time Settings */
static int nbuttons = DEF_NBUTTONS; /* How many buttons to use           */
static int min_len = -1;            /* Min combination length to find    */
static int max_len = -1;            /* Max combination length to find    */
static int verbose_out = 0;         /* Make output verbose               */
static int dump_dag = 0;            /* Dump the DAG once built           */
static int percent = 0;             /* Print percentage of keyspace      */
static int print_count = 0;         /* Print key count at each sequence  */
static int keystried = 0;           /* Number of keys tried              */
static int keystotal = 0;           /* Number of keys total              */
static int colorize = 0;            /* Colorize the DAG dump             */
static int randomize = 0;           /* Randomize the search sequence     */
static int count_width = -1;        /* Width to properly justify count   */
static char count_fmt[64];          /* Format string to print justified
                                       count                             */

static char *buttons = NULL;        /* To hold valid buttons             */

/* Our data structure */
static int ncombs = -1;
static comb_t *combs = NULL;
//static unsigned long sequence_no = 0;
static unsigned long sequence_no = 1;

/* Quick hack so that verbose will prepend # only to lines that follow   */
/* an output with a new-line at the end.                                 */
static int last_nl = 1;

/* Buffer to for output to accumulate, should probably be malloc'd       */
static char output_buff[8192];
static int buffsize = 0;

/*************************************************************************/
/***************************** DECLERATIONS ******************************/
/*************************************************************************/

static void *mmalloc( size_t s );
static int verbose( const char *fmt, ... );
static char diff( const char *a, const char *b );
static void initButtons( void );
static void destroyButtons( void );
static void populateCombination( const char * in );
static void destroyCombinations( void );
static void genCombinations( char *arr, int n, int r );
static void combinationUtil( char *arr, char *data, int start, int end,
    int index, int r );
static int unvisitedCount( comb_t *n );
static void genDAG( void );
static void dumpDAG( void );
static void crackDAG( comb_t *c, const char *parent );
static int bufferOutput( const char *fmt, ... );
void endSequence( void );
static int allVisited( int output );
static const char *basename( const char *in );
static void usage( const char *p, int ret );
int numcheck( const char *arg );
void checkarg( const char *arg, char opt, const char *name );

/*************************************************************************/
/****************************** FUNCTIONS ********************************/
/*************************************************************************/

/*************************************************************************/
/*                                                                       */
/* Function: mmalloc                                                     */
/*                                                                       */
/* A wrapper for malloc to catch errors. It would turn out that we ended */
/* up not doing all that much malloc'ing because 1) it slows things down */
/* badly and 2) it just wasn't necessary.                                */
/*                                                                       */
/* Inputs:                                                               */
/*     s : size of buffer to allocate                                    */
/*                                                                       */
/* Returns:                                                              */
/*     void * : the address of the buffer allocated                      */
/*                                                                       */
/*************************************************************************/
 
static inline void *mmalloc( size_t s ) {

    void *out;

    if( (out = malloc(s)) == NULL ) {
        fprintf(stderr,"Could not allocate memory.\n");
        abort();
    }

    return out;
}

/*************************************************************************/
/*                                                                       */
/* Function: verbose                                                     */
/*                                                                       */
/* Outputs a verbose/debugging line on stdout if the global variable     */
/* `verbose_out` is set. Additionally, if we're being asked to dump the  */
/* DAG, prefixes the line with a '#' so that the output can still be     */
/* piped directly to GraphVIZ.                                           */
/*                                                                       */
/* Inputs:                                                               */
/*     fmt : printf(3) style format string                               */
/*     ... : Variable arguments list                                     */
/*                                                                       */
/* Returns:                                                              */
/*     int : The number of characters printed to stdout                  */
/*                                                                       */
/*************************************************************************/

static int verbose( const char *fmt, ... ) {

    va_list ap;
    int out = 0;

    /* Don't output anything unless verbose is turned on */
    if(!verbose_out)
        return 0;

    /* If we're dumping the DAG, we want our verbose output
     * to have a comment character (#) in it so that our output
     * can be fed directly to dot. */
    if( dump_dag && last_nl )
        out += printf("# ");

    va_start(ap, fmt); /* Init variable args */
    out += vprintf(fmt,ap); /* Print output */
    va_end(ap); /* Destroy variable args */

    /* If the last printed line didn't end in a '\n', remember
     * that so that we don't put another # in the output if
     * we're dumping the DAG. */
    if( fmt[strlen(fmt)-1] == '\n' )
        last_nl = 1;
    else
        last_nl = 0;
   
    fflush(stdout);
 
    return out; /* Does anybody pay attention to the return
                 * value from printf? */
}
    
/*************************************************************************/
/*                                                                       */
/* Function: diff                                                        */
/*                                                                       */
/* Determines the single character difference between two combinations.  */
/* Used to figure out what button was pressed to arrive at the           */
/* particular node in the graph. Since nodes have many parents, this     */
/* was simply the easiest way to accomplish that.                        */
/*                                                                       */
/* Inputs:                                                               */
/*     a : The child (longer) node name.                                 */
/*     b : The parent (shorter) node name.                               */
/*                                                                       */
/* Returns:                                                              */
/*     char : the single letter difference between `a` and `b`           */
/*                                                                       */
/*************************************************************************/

static char diff( const char *a, const char *b ) {

    int i, j, f;

    for( i = 0; i < strlen(a); i++ ) {
        for( j = 0, f = 0; j < strlen(b) && !f; j++ ) {
            if(a[i]==b[j])
                f = 1; /* mark if found */
        }
        if(!f) /* If we didn't find that character, that's our diff */
            return a[i];
    }
    abort(); /* Is an error if we ever get here */
}

/*************************************************************************/
/*                                                                       */
/* Function: initButtons                                                 */
/*                                                                       */
/* Allocates a buffer for, and populates, the available buttons on the   */
/* hypothetical lock. Used to send to the combination generator.         */
/*                                                                       */
/* Inputs: none                                                          */
/*                                                                       */
/* Returns: none                                                         */
/*                                                                       */
/*************************************************************************/

static void initButtons( void ) {
    
    int i;

    if( buttons != NULL )
        abort(); /* This is an error */

    buttons = mmalloc(sizeof(char)*nbuttons+1);
    bzero(buttons,sizeof(char)*nbuttons+1);

    for( i = 0; i < nbuttons; i++ )
        buttons[i] = 'A'+i;
}

/*************************************************************************/
/*                                                                       */
/* Function: destroyButtons                                              */
/*                                                                       */
/* Deallocates and destroys the button structure produced by initButtons */
/*                                                                       */
/* Inputs: none                                                          */
/*                                                                       */
/* Returns: none                                                         */
/*                                                                       */
/*************************************************************************/

static void destroyButtons( void ) {
    bzero(buttons,sizeof(char)*nbuttons);
    free(buttons);
    buttons = NULL;
}

/*************************************************************************/
/*                                                                       */
/* Function: genDAG                                                      */
/*                                                                       */
/* Generates the DAG structure by linking parents to children. This was  */
/* certainly easier to write as a linear function rather than recursive, */
/* however, I don't know if that's the most optimal way to do it.        */
/*                                                                       */
/* Inputs: none                                                          */
/*                                                                       */
/* Returns: none                                                         */
/*                                                                       */
/*************************************************************************/

static void genDAG( void ) {

    int i, j, k, l, m, level;
    comb_t *parent;
    char p[32];

    for( i = 1; i < ncombs; i++ )
    {
        bzero(p,32);

        /* Figure out the level of the graph were on */
        level = strlen(combs[i].name);

        /* Calculate what our last count will be when we start */
        combs[i].last_count = nbuttons - strlen(combs[i].name) + 1;

        for(j = 0; j < level; j++) {
            parent = NULL;
            /* Generate the name of all parents by removing a character
             * one at a time from our name */ 
            for( k = 0, l = 0; k < level; k++ )
                if( k != j ) {
                    p[l] = combs[i].name[k]; 
                    l++;
                }
            /* Hunt down the parent by name */
            for( m = i-1; m >= 0 && parent == NULL; m-- )
                if( strcmp(combs[m].name,p) == 0 )
                    parent = &combs[m];

            /* Find an empty slot in parents next[] array */
            for( m = 0; parent->next[m] != NULL; m++ );

            /* Add this node to the end of the parent's next[] list */
            parent->next[m] = &combs[i];
            parent->num_children++;
        }
    }
}

/*************************************************************************/
/*                                                                       */
/* Function: unvisitedCount                                              */
/*                                                                       */
/* Returns the maximum number of unvisited nodes, including ours,        */
/* reachable from here.                                                  */
/*                                                                       */
/* Inputs:                                                               */
/*        n : pointer to the combination node we're currently analyzing  */
/*                                                                       */
/* Returns:                                                              */
/*     int : Maximum number of defeatable nodes, including ours, below   */
/*           us                                                          */
/*                                                                       */
/*************************************************************************/

static int unvisitedCount( comb_t *n ) {

    int i, tmp, out = 0, max = 0;

    /* Return 0 if we've already once exhausted a deep search OR if the
     * combination size of this node is greater than the max_len
     * requested by the user. */
    if( n->last_count == 0 || strlen(n->name)>max_len )
        return 0;

    /* If we've already been counted in this sequence, just return what
     * we already know. */
    if( n->last_seq == sequence_no )
        return n->last_count;

    /* If we've never been visited ourselves, that's one */
    if( !n->visited ) 
        out++;
   
    /* Find the maximum unvisited node count below us */ 
    for( i = 0; n->next[i] != NULL; i++ ) {
        tmp = unvisitedCount(n->next[i]);
        max = (tmp > max ? tmp : max);
    }

    /* Save our count so we don't keep redoig the same work */
    n->last_seq = sequence_no;
    n->last_count = out+max;

    /* Return the size of our longest defeatable combination string */
    return n->last_count;
}

/*************************************************************************/
/*                                                                       */
/* Function: dumpDAG                                                     */
/*                                                                       */
/* Dumps the DAG in DOT format.                                          */
/*                                                                       */
/* Inputs: none                                                          */
/*                                                                       */
/* Returns: none                                                         */
/*                                                                       */
/*************************************************************************/

static void dumpDAG( void ) {

    int i, j;

    /* Print the graph header */
    printf("digraph {\n");
    printf("    labelloc = \"t\";\n");
    printf("    label = \"n = %d\";\n", nbuttons);

    if( ncombs == 1 )
        printf("    \"*\"\n"); /* If we only have the root, just print
                                * this. */

    for( i = 0; i < ncombs; i++ ) {
        if (colorize) {
            printf("    ");
            if( strlen(combs[i].name) == 0 ) {
                if( combs[i].valid ) 
                    printf("\"*\" [color=green, fontcolor=green];\n");
                else
                    printf("\"*\" [color=red, fontcolor=red];\n");
            } else {
                if( combs[i].valid ) 
                    printf("%s [color=green, fontcolor=green];\n",
                        combs[i].name);
                else
                    printf("%s [color=red, fontcolor=red];\n",
                        combs[i].name);
            }
        }
        for( j = 0; combs[i].next[j] != NULL; j++ ) {
            printf("    "); /* Tab */
            if (strlen(combs[i].name) == 0) 
                printf("\"*\" -> "); /* Root */
            else 
                printf("%s -> ", combs[i].name); /* Node name */

            printf("%s;\n", combs[i].next[j]->name); /* Child */
        }
    }

    printf("}\n"); /* End of the graph */
}

/*************************************************************************/
/*                                                                       */
/* Function: bufferOutput                                                */
/*                                                                       */
/* Accumulates printed output during DAG traversal so that stats, if     */
/* requested, can be prepended to the line in a justified manner.        */
/*                                                                       */
/* Inputs:                                                               */
/*     fmt : printf(3) style format string                               */
/*     ... : Variable arguments list                                     */
/*                                                                       */
/* Returns:                                                              */
/*     int : The number of characters printed to stdout                  */
/*                                                                       */
/*************************************************************************/

static int bufferOutput( const char *fmt, ... ) {
    int c;
    va_list ap;

    if( fmt == NULL || strlen(fmt) == 0 )
        return 0;

    va_start(ap,fmt);
    c = vsnprintf(&output_buff[buffsize], 8192-buffsize, fmt, ap);
    buffsize += c;
    if( buffsize >= 8190 )
        abort();

    output_buff[buffsize] = 0;

    return c;
}

/*************************************************************************/
/*                                                                       */
/* Function: crackDAG                                                    */ 
/*                                                                       */
/* Exhaustively brute-forces the DAG structure to visit all nodes at     */
/* a minimum number of times, and at least once.                         */
/*                                                                       */
/* The strategy works as follows: At each node, find the child that has  */
/* the most number of unvisted nodes below it and descend into that      */
/* node.                                                                 */
/*                                                                       */
/* As a quirk of the algorithm, the head of the structure has to loop    */
/* through its children until the work is complete. All lower nodes do   */
/* not need to do this.                                                  */
/*                                                                       */
/* Inputs:                                                               */
/*          c : current combination node in the graph                    */
/*     parent : name of the parent. Used to calculate the button that    */
/*              was pressed to get from the parent to this node.         */
/*                                                                       */
/* Returns: none                                                         */
/*                                                                       */
/*************************************************************************/

static void crackDAG( comb_t *c, const char *parent ) {

    int i, v, max, nchoices = 0, loop = 0;
    comb_t *next;
    comb_t *choices[32];

    /* Special handling for the head */
    if( strlen(c->name) == 0 ) {
        loop=1;
        if( c->valid ) {
            keystried++;
            bufferOutput( "* ");
        }
        c->visited=1;
    } else {
        bufferOutput("%c",diff(c->name,parent));
        if( !c->visited ) {
            if( c->valid ) {
                keystried++;
                bufferOutput(" * ");
            }
            c->visited = 1;
        }
    }

    if( c->num_children <= 0 || max_len == 0 ) {
        endSequence();
        return;
    }

    do { /* The root of the tree needs to loop through its leaf nodes
          * until everything has been visited. All other traversals do
          * not need to do this. */

        max = 0;
        next = NULL;

        if( randomize )
            nchoices = 0;

        for( i = 0; i < c->num_children; i++ ) {
            /* Get the unvisited count below us */
            v = unvisitedCount(c->next[i]);
            if( v > max ) { /* If it's biggest, keep track of it */
                max = v;
                if( randomize ) {
                    bzero(choices, sizeof(comb_t *) * 32 );
                    choices[0] = c->next[i];
                    nchoices = 1;
                }
                else
                    next = c->next[i];
            } else if( randomize && v > 0 && v == max ) {
                choices[nchoices] = c->next[i];
                nchoices++;
            }
        }

        /* If there's something below us to look at, go look at it */
        if( randomize && nchoices > 0 ) {
            int s = rand()%nchoices;
            crackDAG(choices[s], c->name);
        } else if( !randomize && next != NULL ) {
            crackDAG(next, c->name);
        }

        if( max == 0 && !loop ) {/* we've reached the end of a sequence */
            endSequence();
        }

    } while( loop && max > 0 );
}

/*************************************************************************/
/*                                                                       */
/* Function: endSequence                                                 */
/*                                                                       */
/* Prints the end of a combination sequence, plus any additional percent */
/* or count outputs as requested.                                        */
/*                                                                       */
/* Inputs: none                                                          */
/*                                                                       */
/* Returns: none                                                         */
/*                                                                       */
/*************************************************************************/

void endSequence( void ) {

    /* Are we printing any statistics */
    if( percent || print_count ) {

        printf("(");

        if( percent )
            printf("%5.1f%%", 100.0 * (double)keystried / 
                (double)keystotal);

        if( percent && print_count )
            printf(", ");

        if( print_count ) {

            if( count_width == -1 ) {

                count_width = snprintf(NULL, 0, "%d", keystotal);

                if( snprintf(count_fmt, 64, "%%%dd/%%%dd", count_width,
                    count_width) >= 64 )
                    abort();
            }

            printf(count_fmt, keystried, keystotal);
        }

        printf(") ");
    }

    /* Flush and reset output buffer */
    printf("%s", output_buff);
    output_buff[0] = 0;
    buffsize = 0;

    /* Print the reset symbol */
    printf("->\n");

    /* Increment global sequence number */
    sequence_no++;
}

/*************************************************************************/
/*                                                                       */
/* Function: allVisited                                                  */
/*                                                                       */
/* Iterates through the tree to find out if all nodes have been visited  */
/* yet or not.                                                           */
/*                                                                       */
/* Inputs:                                                               */
/*     output : whether to print errors if there are unvisited nodes     */
/*              or not.                                                  */
/*                                                                       */
/* Returns:                                                              */
/*     int (bool) : 1 if all nodes have been visited. 0 if not           */
/*                                                                       */
/*************************************************************************/

static int allVisited( int output ) {

    int i, ret = 1;

    for( i = 0; i < ncombs; i++ )
        if( !combs[i].visited && combs[i].valid ) {
            if( output ) {
                fprintf(stderr,
                    "WARNING: Combination \"%s\" has not been tried!\n",
                    combs[i].name);
                ret = 0;
            } else {
                return 0;
            }
        }

    return ret;
}

/*************************************************************************/
/*                                                                       */
/* Function: destroyCombinations                                         */
/*                                                                       */
/* Destroys and deallocates the combinations list                        */
/*                                                                       */
/* Inputs: none                                                          */
/*                                                                       */
/* Returns: none                                                         */
/*                                                                       */
/*************************************************************************/

static void destroyCombinations( void ) {

    if( ncombs <= 0 )
        return;

    if( combs != NULL )
        free(combs);

    combs = NULL;
    ncombs = -1;
}

/*************************************************************************/
/*                                                                       */
/* Function: genCombinations                                             */
/*                                                                       */
/* Just a starter location to get the recursion started for generating   */
/* all the possible unique combinations.                                 */
/*                                                                       */
/* Inputs:                                                               */
/*     arr : Array of characters from which to make combinations         */
/*       n : number of elements in arr                                   */
/*       r : length of the combinations to generate                      */
/*                                                                       */
/* Returns: none                                                         */
/*                                                                       */
/*************************************************************************/

static void genCombinations( char *arr, int n, int r ) {

    char data[r]; /* Not sure I agree with allocating this buffer on
                   * the stack... */

    combinationUtil(arr, data, 0, n-1, 0, r); /* Do the work */
}

/*************************************************************************/
/*                                                                       */
/* Function: combinationUtil                                             */
/*                                                                       */
/* Does the heavy lifting when generating all unique mathematical        */
/* combinations of the characters passed.                                */
/*                                                                       */
/* Inputs:                                                               */
/*       arr : Array of characters from which to make combinations       */
/*      data : a temporary data location to keep current combination     */
/*     start : starting index of arr[]                                   */
/*      end  : end index of arr[]                                        */
/*     index : current index in arr[]                                    */
/*         r : size of combination to generate                           */
/*                                                                       */
/* Returns: none                                                         */
/*                                                                       */
/*************************************************************************/

static void combinationUtil( char *arr, char *data, int start, int end,
    int index, int r ) {

    int i, j;
    char *out;

    if( index == r ) {

        out = mmalloc(sizeof(char)*(r+1));
        bzero(out,sizeof(char)*(r+1));

        for( j = 0, i = 0; j < r; j++ ) {
            out[i++]=data[j];
        }
        populateCombination(out);
        free(out);
        return;
    }

    for( i = start; i <= end && end-i+1 >= r-index; i++ )
    {
        data[index] = arr[i];
        combinationUtil(arr, data, i+1, end, index+1, r);
    }
}

/*************************************************************************/
/*                                                                       */
/* Function: populateCombination                                         */
/*                                                                       */
/* Inserts the combination passed into the data structure. Since         */
/* combinations are generated in alphabetical order, we don't have to    */
/* worry about where to insert them.                                     */
/*                                                                       */
/* Inputs:                                                               */
/*     in : sting containing the combination                             */
/*                                                                       */
/* Returns: none                                                         */
/*                                                                       */
/*************************************************************************/

static void populateCombination(const char * in) {

    if( combs == NULL ) {
        combs = mmalloc(sizeof(comb_t)*(1<<nbuttons));
        bzero(combs, sizeof(comb_t)*(1<<nbuttons));
        ncombs = 0;   
    }

    strcpy(combs[ncombs].name,in); /* copy name */
    if( strlen(in) >= min_len && strlen(in) <= max_len ) {
        combs[ncombs].valid = 1; /* Set if it's a valid combo or not */
        keystotal++;
    }

    ncombs++;
}

/*************************************************************************/
/*                                                                       */
/* Function: basename                                                    */
/*                                                                       */
/* Returns the string from everything after the last '/'. This is not    */
/* as fully featured as other implementations.                           */
/*                                                                       */
/* Inputs:                                                               */
/*     in : string containing what we want the basename of               */
/*                                                                       */
/* Returns:                                                              */
/*     char * : the basename of the string                               */
/*                                                                       */
/*************************************************************************/

static const char *basename ( const char *in ) {

    int i;

    if( in == NULL )
        return NULL;

    /* Look for a /. If we find one, return the address of the next
     * character. Otherwise, return the whole string */
    for( i = strlen(in)-2; i > 0; i-- )
        if( in[i] == '/' )
            return &in[i+1];

    return in;
}

/*************************************************************************/
/*                                                                       */
/* Function: usage                                                       */
/*                                                                       */
/* Print usage information on stderr and exit.                           */
/*                                                                       */
/* Inputs:                                                               */
/*      me : String for the exe name from main                           */
/*     ret : Exit code to return on exit                                 */
/*                                                                       */
/* Returns: none                                                         */
/*                                                                       */
/*************************************************************************/

static void usage( const char *me, int ret ) {

    const char *m = (me == NULL ? PROGNAME : me);

    fprintf(stderr,
        "Usage: %s [ -h ] | ( [ -v ] [ -n num ] [ -m min ] [ -x max ] ( ("
            " [ -k ] [ -p ] [ -r ] ) | ( [ -d [ -c ] ] ) ) )\n"
        "    -h : This help message\n"
        "    -n : Number of buttons to brute force, Default: %d\n"
        "    -m : Minimum combination length, Default: %d\n"
        "    -x : Maximum combination length, Default: num\n"
        "    -p : Print percentage of keyspace defeated at each sequence\n"
        "    -k : Print count of keys defeated at each sequence\n"
        "    -r : Randomize the search sequence\n"
        "    -d : Dump the DAG after populating in DOT format\n"
        "    -c : Color the valid/invalid combinations in the DAG dump\n"
        "    -v : Make verbose\n",
        basename(m), DEF_NBUTTONS, DEF_MIN_LEN);

    exit(ret);
}

/*************************************************************************/
/*                                                                       */
/* Function: numcheck                                                    */
/*                                                                       */
/* Checks if argument is numeric. This could probably be a lot smarter.  */
/*                                                                       */
/* Inputs:                                                               */
/*     arg : Argument to check                                           */
/*                                                                       */
/* Returns:                                                              */
/*      int : (bool) whether arg is numeric or not                       */
/*                                                                       */
/*************************************************************************/

int numcheck( const char *arg ) {

    int i;

    if( arg == NULL || strlen(arg) == 0 )
        return 0;

    for( i = 0; i < strlen(arg); i++ )
        if( arg[i] < '0' || arg[i] > '9' )
            return 0;

    return 1;            
}

/*************************************************************************/
/*                                                                       */
/* Function: checkarg                                                    */
/*                                                                       */
/* Checks argument for numeric-ness, outputs an error and calls usage()  */
/* if it's not.                                                          */
/*                                                                       */
/* Inputs:                                                               */
/*     arg : Argument to check                                           */
/*     opt : Option argument was passed to                               */
/*    name : name of program to pass to usage()                          */
/*                                                                       */
/* Returns: none                                                         */
/*                                                                       */
/*************************************************************************/

void checkarg( const char *arg, char opt, const char *name ) {
    if( !numcheck(arg) ) {
        fprintf(stderr,"Error: Option \"%c\" requires a positive integer"
            " argument.\n", opt);
        usage(name,1);
    }
}

/*************************************************************************/
/*                                                                       */
/* Function: main                                                        */
/*                                                                       */
/*************************************************************************/

int main( int argc, char * const argv[], char * const envp[] ) {

    char c;
    int i;

    /* Process out command line options */
    opterr = 0;
    while( (c = (char)getopt(argc, argv, ":n:hm:x:vdpckr")) != -1 ) {
        switch(c) {

            case 'n': /* Number of buttons */
                checkarg(optarg, c, argv[0]);
                nbuttons = atoi(optarg);
                break;

            case 'm': /* Min length */
                checkarg(optarg, c, argv[0]);
                min_len = atoi(optarg);
                break;

            case 'p': /* Percent output */
                percent = 1;
                break;

            case 'k': /* Print counts */
                print_count = 1;
                break;

            case 'r': /* Randomize */
                randomize = 1;
                break;

            case 'x': /* Max length */
                checkarg(optarg, c, argv[0]);
                max_len = atoi(optarg);
                break;

            case 'v': /* Verbose */
                verbose_out++;
                break;
    
            case 'd': /* Dump the DAG instead of brute force */
                dump_dag = 1;
                break;

            case 'c': /* Colorize */
                colorize = 1;
                break;

            case '?': /* Unknown option */
                fprintf(stderr,"Invalid option \"%c\".\n", optopt);
                usage(argv[0], 1);

            case ':': /* Missing argument */
                fprintf(stderr,"Error: Option \"%c\" requires an "
                    "argument.\n", optopt);
                usage(argv[0], 1);
  
            case 'h': /* Help */
                usage(argv[0], 0);

            default: /* In case we forgot something */
                fprintf(stderr,"Unknown option \"%c\".\n", c);
                usage(argv[0], 1);
        }
    }

    if( colorize && ! dump_dag ) {
        fprintf(stderr,"Colorize option not valid unless dumping DAG.\n");
        usage(argv[0],1);
    }

    if( (randomize || print_count || percent) && dump_dag ) {
        fprintf(stderr,"Randomize, count, and percent options are not "
            "valid when dumping DAG.\n");
        usage(argv[0],1);
    }

    /* Check if nbuttons is in a suitable range */
    if( nbuttons > 26 || nbuttons < 0 ) {
        fprintf(stderr,"Number of buttons of \"%d\" is not "
            "valid. Maximum is 26, minimum is 0.\n", nbuttons);
        usage(argv[0],1);
    }

    /* Fix min_len and max_len if needed */
    if( min_len < 0 )
        min_len = DEF_MIN_LEN;
    else if( min_len > nbuttons )
        min_len = nbuttons;

    if( max_len > nbuttons || max_len < min_len )
        max_len = nbuttons;
        
    initButtons(); /* Initialize the button-space */
    verbose("Valid buttons are: \"%s\"\n", buttons);

    /* Generate all unique combinations of the button space */
    verbose("Generating all possible combinations...");
    for( i = 0; i <= nbuttons; i++ ) 
        genCombinations(buttons,nbuttons,i);
    verbose(" done.\n");
    verbose("Generated %d combinations.\n", ncombs);

    /* Build our DAG */
    verbose("Building DAG...");
    genDAG();
    verbose(" done.\n");

    if( dump_dag ) /* Dump it if we've been requested to */
        dumpDAG();
    else {
        if( randomize )
            srand(time(NULL));
        crackDAG(&combs[0],NULL); /* Otherwise, crack it */
        allVisited(1);              /* Sanity check */
    }

    /* Cleanup */
    destroyCombinations();
    destroyButtons();

    if( randomize ) {
        printf("Keep in mind that randomize is broken.\n");
    }
    /* So long, and thanks for all the fish. */
    return 0;

} /* end main() */

#endif /* COMBOCRACK_C */
