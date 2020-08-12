#include <stdio.h>

/*********************************************************
 * Records the extent of each block's payload
 * for evaluate the validity of your allocator
 * DON'T MODIFY THIS STRUCT.
 ********************************************************/
typedef struct range_t {
  char *lo;              /* low payload address */
  char *hi;              /* high payload address */
  struct range_t *next;  /* next list element */
} range_t;

/*
 * Function lists which student should implement.
 */
extern int mm_init (range_t **ranges);
extern void *mm_malloc (size_t size);
extern void mm_free (void *ptr);
extern void mm_exit (void);
extern void *mm_realloc(void *ptr, size_t size);

/*
 * Students work in teams of one.  Teams enter their
 * personal name and student ID in a struct of this
 * type in their mm.c file.
 */
typedef struct {
    char *name;    /* full name of first member */
    char *id;      /* student ID of first member */
} team_t;

extern team_t team;

