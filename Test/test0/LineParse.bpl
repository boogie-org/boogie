// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
#line
#line 
#line 0
#line                     0

#dontknow what this is    No, I don't    well, it's an error is what it is 

#define ASSERT(x) {if (!(x)) { crash(); }}  // error: A B C . txt(12,0)

// this is line 5;  an error occurs on line 6:
 #line 10  // this is not even scanned like a pragma, because the # is not in column 0

