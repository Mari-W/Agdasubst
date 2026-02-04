Welcome to mkbTT!

mkbTT is a Knuth-Bendix completion tool: given a set of input equalities, it
tries to generate a confluent and terminating rewrite system that can decide
the equational theory. mkbTT differs from traditional tools in two respects:
(1) instead of requiring a reduction order as input, it employs modern 
termination tools, and (2) mkbTT uses multi-completion to keep track of 
multiple possible orientations in parallel.
For details, please see http://cl-informatik.uibk.ac.at/mkbtt/.

----------------------------------------------------------------------
                                 USAGE
----------------------------------------------------------------------

Example calls:
  * standard completion
    $ ./mkbtt -s lpo input/KB/BGK94_D08.trs

  * ordered completion needs -o:
    $ ./mkbtt -o -ct input/B91_unfailing_groupoid.trs


  * normalized completion needs -n:
    Without specifying the theory with respect to which normalized completion
    is performed, the largest recognized is chosen, here G (output when using
    option -st):
    $ ./mkbtt -st -ct -n input/ac_group_homo.trs
   
    Limiting the termination technique, as here to acrpo, can be helpful:
    $ ./mkbtt -ct -n -s acrpo input/ac_ring2.trs

    The theory with respect to which normalized completion is performed can be
    controlled with the option -th:
    $ ./mkbtt -ct -n -th input/ac.trs -s acrpo input/ac_group_homo.trs
