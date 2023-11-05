:- set_prolog_flag(double_quotes, chars).
:- use_module(library(dcg/basics)).
:- use_module(library(dcg/high_order)).

parse(String, AST) :-
    phrase((uvl(AST),eos), String).

uvl(ast(H,F,C)) -->
    header(H),
    features(F),
    constraints(C).

header(header(namespace(N),includes(In),imports(Im))) -->
    optional((namespace(N),op_nl),[]),
    optional((includes(In),op_nl),[]),
    optional((imports(Im),op_nl),[]).

namespace(N) --> "namespace", blanks, string(N).

includes(I) --> "include ", blanks, remainder(I).
imports(I) --> [].
features(F) --> [].
constraints(C) --> [].

op_nl --> optional("\n",[]).
op_nl --> optional("\r\n",[]).
