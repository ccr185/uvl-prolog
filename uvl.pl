:- module(uvl, [parse/3]).
:- set_prolog_flag(double_quotes, string).
:- set_prolog_flag(encoding, utf8).
:- encoding(utf8).
:- use_module(library(dcg/basics)).
:- use_module(library(dcg/high_order)).
:- use_module(lexer).
:- use_module(library(tabling)).
:- use_module(library(clpfd)).

%%Main entrypoint for the parser for UVL files
%%Is conformant to the grammar as defined in the uvl-parser
%%repository
parse(File, AST, Stop) :-
    lex_uvl(Tokens, File), !,
    phrase(uvl(AST), Tokens, Stop).

uvl(ast(H,F,C)) -->
    header(H),
    optional(features(F),{F = nil}),
    optional(constraints(C),{C = nil}).

header(header(namespace(N),includes(In),imports(Im))) -->
    optional(namespace(N),{N = []}),
    optional(includes(In),{In = []}),
    optional(imports(Im),{Im = []}).

namespace(N) --> [namespace], reference(N), !.
reference(N) --> ([id_strict(N)], !) | ([id_not_strict(N)], !).
fully_qualified_reference(FQN) --> sequence(reference, [dot], FQN), {length(FQN, Len), Len #> 0}.

includes(Is) --> [include, indent], includes_(Is), [dedent].
includes_([I|Is]) --> language_level(I), !, includes_(Is).
includes_([]) --> [].

language_level(lang_level(Major,Minor)) -->
    major_level(Major), optional(minor_level(Minor), {Minor = []}).

major_level(Major) -->
    ([boolean_t], {Major = boolean_level}, ! ) |
    ([arithmetic_t], {Major = arithmetic_level}, ! ) |
    ([type_t], {Major = type_level}, ! ).
minor_level(Minor) -->
    [dot], !, (
        ([group_card], {Minor = group_card}, !) |
        ([feature_card], {Minor = feature_card}, !) |
        ([agg_fun], {Minor = agg_fun}, !) |
        ([string_constraints], {Minor = string_constraints}, !) |
        ([mul], {Minor = minor_all}, !)
    ).

imports(Is) --> [imports, indent], imports_(Is), [dedent].
imports_([import(NS,Alias)|Is]) -->
    reference(NS),
    optional(([as], reference(Alias)), {Alias = []}), !,
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
    optional(([indent], groups(Gs), [dedent]), {Gs = nil}), !,
    features_(Fs).
features_([]) --> [].

feature_type(boolean) --> [boolean_t], !.
feature_type(integer) --> [integer_t], !.
feature_type(string) --> [string_t], !.
feature_type(real) --> [real_t], !.

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
    (value_attr(A) | constraint_attr(A)), [comma], !, attributes_(As).
attributes_([A]) --> (value_attr(A) | constraint_attr(A)), !.
attributes_([]) --> [], !.

value_attr(attr(key(K),val(V))) -->
    id(K), optional(value(V), {V = nil}).

value(bool(B)) --> [boolean(B)], !.
value(integer(I)) --> [integer(I)], !.
value(float(F)) --> [float(F)], !.
value(string(S)) --> [normal_string(S)], !.
value(attributes(Attrs)) --> attributes(Attrs), !.
value(vector(V)) --> [lbracket], vector(V), [rbracket], !.

vector([V|Vs]) --> value(V), [comma], !, vector(Vs).
vector([V]) --> value(V), !.
vector([]) --> [], !.

groups([G|Gs]) --> group(G), !, groups(Gs).
groups([]) --> [].

group(or_group(S)) -->  [or_group], group_spec(S), !.
group(alternative(S)) --> [alternative], group_spec(S), !.
group(optional(S)) --> [optional], group_spec(S), !.
group(mandatory(S)) --> [mandatory], group_spec(S), !.
group(cardinality(Card,S)) --> cardinality(Card), group_spec(S), !.

group_spec(Fs) --> [indent], features_(Fs), {length(Fs,L), L > 0}, [dedent].

constraint_attr(C) --> [constraint], constraint(C), !.
constraint_attr(Cs) --> [constraints], constraint_list(Cs), !.

:- table constraint/3.

constraint(equation(E)) --> equation(E), !.
constraint(paren_constraint(C)) --> [lparen], constraint(C), [rparen], !.
constraint(not_constraint(C)) --> [not], constraint(C), !.
constraint(and_constraint(C1,C2)) --> constraint(C1), [and], constraint(C2), !.
constraint(or_constraint(C1,C2)) --> constraint(C1), [or], constraint(C2), !.
constraint(impl_constraint(C1,C2)) --> constraint(C1), [impl], constraint(C2), !.
constraint(eq_constraint(C1,C2)) --> constraint(C1), [equivalence], constraint(C2), !.
constraint(literal_constraint(C)) --> fully_qualified_reference(C).

constraint_list(Cs) --> [lbracket], constraint_list_(Cs), [rbracket].
constraint_list_([C|Cs]) --> constraint(C), [comma], !, constraint_list_(Cs).
constraint_list_([C]) --> constraint(C), !.
constraint_list_([]) --> [], !.

constraints(Cs) --> [constraints, indent], constraints_(Cs), [dedent].
constraints_([C|Cs]) --> constraint(C), !, constraints_(Cs).
constraints_([]) --> [].

:- table equation/3.

equation(equal(E1,E2)) --> expression(E1), [equal], expression(E2), !.
equation(lt(E1,E2)) --> expression(E1), [lt], expression(E2), !.
equation(gt(E1,E2)) --> expression(E1), [gt], expression(E2), !.
equation(lte(E1,E2)) --> expression(E1), [lte], expression(E2), !.
equation(gte(E1,E2)) --> expression(E1), [gte], expression(E2), !.
equation(neq(E1,E2)) --> expression(E1), [neq], expression(E2), !.

:- table expression/3.

expression(E) --> ([float(E)] | [integer(E)] | [string(E)]), !.
expression(E) --> aggregate_function(E), !.
expression(E) --> fully_qualified_reference(E).
expression(sub_expression(E)) --> [lparen], expression(E), [rparen].
expression(add(E1,E2)) --> expression(E1), [add], expression(E2), !.
expression(sub(E1,E2)) --> expression(E1), [sub], expression(E2), !.
expression(mul(E1,E2)) --> expression(E1), [mul], expression(E2), !.
expression(div(E1,E2)) --> expression(E1), [div], expression(E2), !.

aggregate_function(sum(ref(R),ref_op(ROP))) -->
    [sum, lparen], optional((fully_qualified_reference(ROP),[comma]), {ROP = nil}),
    fully_qualified_reference(R), [rparen], !.
aggregate_function(avg(ref(R),ref_op(ROP))) -->
    [avg, lparen], optional((fully_qualified_reference(ROP),[comma]), {ROP = nil}),
    fully_qualified_reference(R), [rparen], !.
aggregate_function(len(ref(R))) -->
    [len, lparen], fully_qualified_reference(R), [rparen], !.
aggregate_function(floor(ref(R))) -->
    [floor, lparen], fully_qualified_reference(R), [rparen], !.
aggregate_function(ceil(ref(R))) -->
    [ceil, lparen], fully_qualified_reference(R), [rparen], !.

id(ID) --> [id_strict(ID)] | [id_not_strict(ID)].
