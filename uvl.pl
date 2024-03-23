:- module(uvl, [parse/3]).
:- set_prolog_flag(double_quotes, string).
:- set_prolog_flag(encoding, utf8).
:- encoding(utf8).
:- use_module(library(dcg/basics)).
:- use_module(library(dcg/high_order)).
:- use_module(lexer).
%:- use_module(library(tabling)).
:- use_module(library(clpfd)).

%%Main entrypoint for the parser for UVL files
%%Is conformant to the grammar as defined in the uvl-parser
%%repository
parse(File, AST, Stop) :-
    lex_uvl(Tokens, File), !,
    phrase(uvl(AST), Tokens, Stop).

test_tokens(
    [
        features,indent,id_strict("Sandwich"),indent,mandatory,indent,id_strict("Bread"),dedent,
        optional,indent,id_strict("Sauce"),indent,alternative,indent,id_strict("Ketchup"),
        id_strict("Mustard"),dedent,dedent,id_strict("Cheese"),dedent,dedent,dedent,constraints,
        indent,id_strict("Ketchup"),impl,id_strict("Cheese"),dedent
    ]
).

test_parse(AST) :-
    test_tokens(Ts),
    phrase(uvl(AST), Ts).


uvl(ast(H,F,C)) -->
    header(H),
    optional(features(F),{F = nil}),
    optional(constraints(C),{C = nil}).

header(header(namespace(N),includes(In),imports(Im))) -->
    optional(namespace(N),{N = []}),
    optional(includes(In),{In = []}),
    optional(imports(Im),{Im = []}).

namespace(N) --> [namespace], reference(N).
reference(N) --> ([id_strict(N)]) | ([id_not_strict(N)]).
fully_qualified_reference(FQN) --> sequence(reference, [dot], FQN), {length(FQN, Len), Len #> 0}.

includes(Is) --> [include, indent], includes_(Is), [dedent].
includes_([I|Is]) --> language_level(I), includes_(Is).
includes_([]) --> [].

language_level(lang_level(Major,Minor)) -->
    major_level(Major), optional(minor_level(Minor), {Minor = []}).

major_level(Major) -->
    ([boolean_t], {Major = boolean_level} ) |
    ([arithmetic_t], {Major = arithmetic_level} ) |
    ([type_t], {Major = type_level} ).
minor_level(Minor) -->
    [dot], (
        ([group_card], {Minor = group_card}) |
        ([feature_card], {Minor = feature_card}) |
        ([agg_fun], {Minor = agg_fun}) |
        ([string_constraints], {Minor = string_constraints}) |
        ([mul], {Minor = minor_all})
    ).

imports(Is) --> [imports, indent], imports_(Is), [dedent].
imports_([import(NS,Alias)|Is]) -->
    reference(NS),
    optional(([as], reference(Alias)), {Alias = []}),
    imports_(Is).
imports_([]) --> [].

features(Fs) --> [features, indent], features_(Fs), [dedent].
features_(
    [feature(
        name(N), type(FeatureType), cardinality(Card),
        attributes(Attrs), group(Gs)
    )|Fs]
) -->
    optional(feature_type(FeatureType), {FeatureType = boolean}),
    fully_qualified_reference(N),
    optional(feature_cardinality(Card), {Card = nil}),
    optional(attributes(Attrs), {Attrs = nil}),
    optional(([indent], groups(Gs), [dedent]), {Gs = nil}),
    features_(Fs).
features_([]) --> [].

feature_type(boolean) --> [boolean_t].
feature_type(integer) --> [integer_t].
feature_type(string) --> [string_t].
feature_type(real) --> [real_t].

feature_cardinality(card(From,To)) -->
    [cardinality, lbracket, integer(From)],
    optional(([range], ([integer(To)] | ([mul], {To = inf}))), {To = nil}),
    [rbracket].
cardinality(card(From,To)) -->
    [lbracket, integer(From)],
    optional(([range], ([integer(To)] | ([mul], {To = inf}))), {To = nil}),
    [rbracket].

attributes(Attrs) --> [lbrace], attributes_(Attrs), [rbrace].
attributes_([A|As]) -->
    (value_attr(A) | constraint_attr(A)), [comma], attributes_(As).
attributes_([A]) --> (value_attr(A) | constraint_attr(A)).
attributes_([]) --> [].

value_attr(attr(key(K),val(V))) -->
    id(K), optional(value(V), {V = nil}).

value(bool(B)) --> [boolean(B)].
value(integer(I)) --> [integer(I)].
value(float(F)) --> [float(F)].
value(string(S)) --> [normal_string(S)].
value(attributes(Attrs)) --> attributes(Attrs).
value(vector(V)) --> [lbracket], vector(V), [rbracket].

vector([V|Vs]) --> value(V), [comma], vector(Vs).
vector([V]) --> value(V).
vector([]) --> [].

groups([G|Gs]) --> group(G), groups(Gs).
groups([]) --> [].

group(or_group(S)) -->  [or_group], group_spec(S).
group(alternative(S)) --> [alternative], group_spec(S).
group(optional(S)) --> [optional], group_spec(S).
group(mandatory(S)) --> [mandatory], group_spec(S).
group(cardinality(Card,S)) --> cardinality(Card), group_spec(S).

group_spec(Fs) --> [indent], features_(Fs), {length(Fs,L), L > 0}, [dedent].

constraint_attr(C) --> [constraint], constraint(C).
constraint_attr(Cs) --> [constraints], constraint_list(Cs).

%:- table constraint/3.

constraint(equation(E)) --> equation(E).
constraint(paren_constraint(C)) -->
    [lparen], constraint(C),
    %{abolish_all_tables},
    [rparen].
constraint(not_constraint(C)) --> [not], constraint(C). %, {abolish_all_tables}.
constraint(and_constraint(C1,C2)) -->
    constraint(C1), [and],
    %{abolish_all_tables},
    constraint(C2).
    %{abolish_all_tables}.
constraint(or_constraint(C1,C2)) -->
    constraint(C1),
    %{abolish_all_tables},
    [or], constraint(C2).
    %, {abolish_all_tables}.
constraint(impl_constraint(C1,C2)) -->
    constraint(C1),
    %{abolish_all_tables},
    [impl], constraint(C2).
    %, {abolish_all_tables}.
constraint(eq_constraint(C1,C2)) -->
    constraint(C1),
    %{abolish_all_tables},
    [equivalence], constraint(C2).
    %{abolish_all_tables}.
constraint(literal_constraint(C)) --> fully_qualified_reference(C).

constraint_list(Cs) --> [lbracket], constraint_list_(Cs), [rbracket].
constraint_list_([C|Cs]) -->
    constraint(C),
    %{abolish_all_tables},
    [comma], constraint_list_(Cs).
constraint_list_([C]) --> constraint(C).%, {abolish_all_tables}.
constraint_list_([]) --> [].

% TODO: Handle all the occurrences of contraint//1 so that it point here instead

c(constraint(op(Op), left(equation(E)), right(C), next(N))) --> equation(E), cp(tail(op(Op), C, N)).
c(constraint(op(Op), left(paren(CL)), right(CR), next(N))) --> [lparen], c(CL), [rparen], cp(tail(op(Op), CR, N)).
%%%The not is super problematic because it recurses and breaks the operand chain
%%%The best way to deal with it is to bind it super tightly to the three actual Cs
%%% TODO: Make suret this can be generalized correctly!!!
c(constraint(op(Op), left(not(CN)), right(C), next(N))) --> [not], fully_qualified_reference(R),
                                                            {CN = constraint(op(nil),left(literal(R)),right(nil),next(nil))}, cp(tail(op(Op), C, N)).
c(constraint(op(Op), left(not(CN)), right(C), next(N))) --> [not], c(CN), cp(tail(op(Op), C, N)).
c(constraint(op(Op), left(literal(L)), right(C), next(N))) --> fully_qualified_reference(L), cp(tail(op(Op), C, N)).

cp(tail(op(and), C, Next)) --> [and], c(C), cp(Next).
cp(tail(op(or), C, Next)) --> [or], c(C), cp(Next).
cp(tail(op(impl), C, Next)) --> [impl], c(C), cp(Next).
cp(tail(op(equivalence), C, Next)) --> [equivalence], c(C), cp(Next).
cp(tail(op(nil), nil, nil)) --> [].

test_constraint(C) :-
    C = constraint(
        op(or),
        left(literal([TREE_RCU])),
        right(constraint(
            op(or),
            left(literal([TREE_PREEMPT_RCU])),
            right(constraint(
                op(or),
                left(not(constraint(
                    op(nil),
                    left(literal([RCU_TRACE])),
                    right(nil),
                    next(nil)))),
                right(constraint(
                    op(or),
                    left(not(constraint(
                        op(nil),
                        left(literal([TEST])),
                        right(nil),
                        next(nil)))),
                    right(constraint(
                        op(nil),
                        left(literal([T2])),
                        right(nil),
                        next(nil))),
                    next(tail(op(nil),nil,nil)))),
                next(tail(op(nil),nil,nil)))),
            next(tail(op(nil),nil,nil)))),
        next(tail(op(nil),nil,nil))).

test_constraint2(C) :-
    C = a.

rebalance_constraint(C, RC) :-
    r_c(C,RC).

r_c(constraint(op(O),left(L),right(nil),next(N)),constraint(op(O),left(L),right(nil),next(N))).
r_c(constraint(op(O),left(L),right(R),next(N)), RC) :-
    dif(R,nil),
    l_r(constraint(op(O),left(L),right(R),next(N)),RC0),
    r_c(RC0,RC).

%left rotate
l_r(constraint(op(nil),left(L),right(R),next(N)), constraint(op(nil),left(L),right(R),next(N))).
l_r(constraint(op(Op0), left(L0), right(R0), next(N0)), constraint(op(Op),left(L),right(R),next(N))) :-
    dif(Op0,nil), R0 = nil, Op = Op0, L = L0, R = R0, N0 = N.
l_r(constraint(op(Op0), left(L0), right(R0), next(N0)), constraint(op(Op),left(L),right(R),next(N1))) :-
    dif(R0,nil),
    R0 = constraint(op(Op),left(L1),right(R1),next(N1)),
    L = constraint(op(Op0),left(L0),right(L1),next(N0)),
    R = R1.

constraints(Cs) --> [constraints, indent], constraints_(Cs), [dedent].
constraints_([C|Cs]) -->
    %constraint(C),
    c(C0),
    {debug(parser,'Parsed constraint ~w', [C0])}, {r_c(C0,C)},
    {debug(parser,'Rebalanced to ~w',[C])},
    %{abolish_table_subgoals(constraint(C))},
    {abolish_private_tables},
    {abolish_table_subgoals(constraint(_,_,_)), abolish_table_subgoals(equation(_,_,_)), abolish_table_subgoals(expression(_,_,_))},
    constraints_(Cs).
constraints_([]) --> [].

%:- table equation/3.

equation(equal(E1,E2)) -->
    %expression(E1),
    e, [equal], e.
    %expression(E2).
equation(lt(E1,E2)) -->
    %expression(E1),
    e, [lt], e.
    %expression(E2).
equation(gt(E1,E2)) -->
    %expression(E1),
    e, [gt], e.
    %expression(E2).
equation(lte(E1,E2)) -->
    %expression(E1),
    e, [lte], e.
    %expression(E2).
equation(gte(E1,E2)) -->
    %expression(E1),
    e, [gte], e.
    %expression(E2).
equation(neq(E1,E2)) -->
    %expression(E1),
    e, [neq], e.
    %expression(E2).

%:- table expression/3.

expression(E) --> ([float(E)] | [integer(E)] | [string(E)]).
expression(E) --> aggregate_function(E).
expression(E) --> fully_qualified_reference(E).
expression(sub_expression(E)) --> [lparen], expression(E), [rparen].
expression(add(E1,E2)) --> expression(E1), [add], expression(E2).
expression(sub(E1,E2)) --> expression(E1), [sub], expression(E2).
expression(mul(E1,E2)) --> expression(E1), [mul], expression(E2).
expression(div(E1,E2)) --> expression(E1), [div], expression(E2).

% TODO: Fix expressions and create the parse tree for them.

e --> [float(E)], ep.
e --> [integer(E)], ep.
e --> [string(E)], ep.
e --> aggregate_function(E), ep.
e --> [lparen], e, [rparen], ep.

ep --> [add], e, ep.
ep --> [sub], e, ep.
ep --> [mul], e, ep.
ep --> [div], e, ep.
ep --> [].

aggregate_function(sum(ref(R),ref_op(ROP))) -->
    [sum, lparen], optional((fully_qualified_reference(ROP),[comma]), {ROP = nil}),
    fully_qualified_reference(R), [rparen].
aggregate_function(avg(ref(R),ref_op(ROP))) -->
    [avg, lparen], optional((fully_qualified_reference(ROP),[comma]), {ROP = nil}),
    fully_qualified_reference(R), [rparen].
aggregate_function(len(ref(R))) -->
    [len, lparen], fully_qualified_reference(R), [rparen].
aggregate_function(floor(ref(R))) -->
    [floor, lparen], fully_qualified_reference(R), [rparen].
aggregate_function(ceil(ref(R))) -->
    [ceil, lparen], fully_qualified_reference(R), [rparen].

id(ID) --> [id_strict(ID)] | [id_not_strict(ID)].
