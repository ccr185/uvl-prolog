:- module(ast, [print_clif_from_ast/2]).
:- set_prolog_flag(double_quotes, string).
:- set_portray_text(enabled, true).
:- use_module(library(dcg/high_order)).
:- use_module(library(portray_text)).
:- use_module(library(apply)).
:- use_module(library(apply_macros)).
:- use_module(library(yall)).
:- use_module(library(error)).
:- use_module(uvl).

print_clif_from_ast(File, CLIFS) :-
    parse(File, AST, []),
    print_term(AST,[]), nl, nl,
    writeln("Parsing Complete"),
    clif_from_ast(CLIF, AST),
    foldl([C,S,NS]>>string_concat(S,C,NS),CLIF,"",CLIFS),
    print_term(CLIFS, []).



clif_from_ast(CLIF, AST) :-
    phrase(ast_gen(AST), CLIF).

ast_gen(
    ast(header(namespace(N),includes(In),imports(Im)),Features,Constraints)
) -->
      feature_sentences(Features, root),
      constraint_sentences(Constraints).

feature_sentences(nil, _) --> [].
feature_sentences([], _) --> [].
feature_sentences([Feature|Fs], HierarchyPosition) -->
    feature_sentence(Feature, HierarchyPosition),
    {HierarchyPosition = root -> HP1 = leaf; HP1 = HierarchyPosition},
    feature_sentences(Fs, HP1).

feature_sentence(
    feature(
        name(N), type(FeatureType), cardinality(Card),
        attributes(Attrs), group(Gs)
    ), HierarchyPosition
) -->
    {normalize_name(N, NN)},
    feature_var_decl(FeatureType, NN, Card, HierarchyPosition),
    %%% Here we would handle the attrs
    feature_attr_sentences(Attrs, NN),
    feature_group_sentences(Gs, NN).

%% Entry
feature_attr_sentences(nil, _) --> [].
feature_attr_sentences([], _) --> [].
feature_attr_sentences([Attr|Attrs], NN) -->
    feature_attr_sentence(Attr, NN),
    feature_attr_sentences(Attrs, NN).

%% Value attr
feature_attr_sentence(attr(key(K),val(V)), NN) -->
    feature_attr_var_decl(K, V, NN).

feature_attr_var_decl(K, nil, NN) --> [""].

% TODO: Take care of normalizing names and fully qualifying them.
normalize_name([FirstN|Ns], NN) :-
    foldl([E,S,NS]>>(string_concat(S,".",S1),string_concat(S1,E,NS)),Ns,FirstN,NN).

feature_var_decl(boolean, N, _, leaf) --> ["(bool ", N, ")"].
feature_var_decl(boolean, N, _, root) --> ["(bool ", N, ")", "(= ", N, " 1)"].
feature_var_decl(integer, N, nil, _) --> ["(int ", N, " )"].
feature_var_decl(integer, N, card(From,To), _) --> ["(int (", From, " ", To, ") ", N, " )"].
feature_var_decl(string, _, _, _).
feature_var_decl(real, _, _, _).

feature_group_sentences(nil, _) --> [].
feature_group_sentences([], _) --> [].
feature_group_sentences([G|Gs], N) -->
    feature_group_sentence(G, N),
    feature_group_sentences(Gs, N).

feature_group_sentence(mandatory(Fs), N) -->
    mandatory_group_sentence(Fs, N).
feature_group_sentence(alternative(Fs), N) -->
    {
        findall(FName, (
            member(Feat,Fs),
            feature_name(Feat,FName)
        ), FNames)
    },
    ["(=< ("], v_sum(FNames), [" ) ", N, " )"],
    feature_sentences(Fs, leaf).
feature_group_sentence(optional(Fs), N) -->
    optional_group_sentence(Fs, N).
feature_group_sentence(or_group(Fs), N) -->
    optional_group_sentence(Fs, N). %% FIX
feature_group_sentence(cardinality(card(From,To),Fs), N) -->
    {
        findall(FName, (
            member(Feat,Fs),
            feature_name(Feat,FName)
        ), FNames)
    },
    ["(=< ( "], v_sum(FNames), [" ) ( ", N, "*", To, " ) )"],
    ["(=< ( ", N, "*", From, " ) ( "], v_sum(FNames), [ " )"],
    feature_sentences(Fs, leaf).

%%This case is probably unnecessary.
v_sum([]) --> [].
v_sum([FName]) --> [FName].
v_sum([FName0, FName1|FNames]) --> [FName0, " + "], v_sum([FName1|FNames]).

%%Rewrite w/ aux predicate
mandatory_group_sentence([], _) --> [].
mandatory_group_sentence([F|Fs], N) -->
    {
        F = feature(
            name(FeatName), type(FeatType), cardinality(Card),
            attributes(Attrs), group(FeatGroups)
        ),
        normalize_name(FeatName,FeatNameNorm)
    },
    ["(= ",N, " ", FeatNameNorm, " )"],
    feature_sentence(F, leaf),
    mandatory_group_sentence(Fs, N).

optional_group_sentence([],_) --> [].
optional_group_sentence([F|Fs], N) -->
    {feature_name(F,FName)},
    ["(>= ", N, " ", FName, ")"],
    feature_sentence(F, leaf),
    optional_group_sentence(Fs,N).

%% Utility
feature_name(feature(name(N),_,_,_,_),NN) :- normalize_name(N,NN).
feature_type(feature(_,type(T),_,_,_),T).
feature_card(feature(_,_,cardinality(Card),_,_),Card).
feature_attr(feature(_,_,_,attributes(Attrs),_),Attrs).
feature_group(feature(_,_,_,_,group(FeatGroups)), FeatGroups).

%% Constraints
%% There is case where there are just no sentences at all
constraint_sentences(nil) --> [].
constraint_sentences([]) --> [].
constraint_sentences([C|Cs]) -->
    constraint_sentence(C),
    constraint_sentences(Cs).

constraint_sentence(equation(E)) --> render_equation(E).
%%N.B. Something tricky happens with this constraint,
%%It just so happens that many translations to UVL treat the literal
%%as a reified constraint, and this trips up the
%%clif parser because a name by itself is generally not allowed
%%since it implies Var = 1. Therefore,
%%for sanity's sake, it makes sense to use the "true constraint"
%%that works for both the propositional case and the more general
%%integer case (and, in particular, it makes the assumption that
%%even if the constraint is an integer, 0 means deselected).
%% constraint_sentence(literal_constraint(C)) --> {normalize_name(C,CN)}, [CN].
constraint_sentence(literal_constraint(C)) -->
    {normalize_name(C,CN)}, ["(>= ", CN, " 1 )"].
constraint_sentence(paren_constraint(C)) --> constraint_sentence(C).
constraint_sentence(not_constraint(C)) -->
    ["(not "], constraint_sentence(C), [" )"].
constraint_sentence(and_constraint(C1,C2)) -->
    ["(and "], constraint_sentence(C1), [" "], constraint_sentence(C2), [" )"].
constraint_sentence(or_constraint(C1,C2)) -->
    ["(or "], constraint_sentence(C1), [" "], constraint_sentence(C2), [" )"].
constraint_sentence(impl_constraint(C1,C2)) -->
    ["(if "], constraint_sentence(C1), [" "], constraint_sentence(C2), [" )"].
constraint_sentence(eq_constraint(C1,C2)) -->
    ["(iff "], constraint_sentence(C1), [" "], constraint_sentence(C2), [" )"].

render_equation(equal(E1,E2)) -->
    ["(= "], render_expression(E1), [" "], render_expression(E2), [")"].
render_equation(lt(E1,E2)) -->
    ["(< "], render_expression(E1), [" "], render_expression(E2), [")"].
render_equation(gt(E1,E2)) -->
    ["(> "], render_expression(E1), [" "], render_expression(E2), [")"].
render_equation(lte(E1,E2)) -->
    ["(=< "], render_expression(E1), [" "], render_expression(E2), [")"].
render_equation(gte(E1,E2)) -->
    ["(>= "], render_expression(E1), [" "], render_expression(E2), [")"].
render_equation(neq(E1,E2)) -->
    ["(!= "], render_expression(E1), [" "], render_expression(E2), [")"].

render_expression(E) -->
    {is_of_type(integer,E); is_of_type(float,E); is_of_type(string,E)}, [E].
render_expression(E) -->
    {is_of_type(list(string),E), normalize_name(E,NE)}, [NE].
%% render_expression(integer(E)) --> [E].
render_expression(string(E)) --> [E]. % Dangerous stuff...
render_expression(sub_expression(E)) -->
    ["( "], render_expression(E), [" )"].
render_expression(add(E1,E2)) -->
    ["(+ "], render_expression(E1), [" "], render_expression(E2), [" )"].
render_expression(sub(E1,E2)) -->
    ["(- "], render_expression(E1), [" "], render_expression(E2), [" )"].
render_expression(mul(E1,E2)) -->
    ["(* "], render_expression(E1), [" "], render_expression(E2), [" )"].
render_expression(div(E1,E2)) -->
    ["(/ "], render_expression(E1), [" "], render_expression(E2), [" )"].

%render aggregate expressions
%These are very tricky
%%%% TODO: Figure out what the hell the aditional ref is supposed to represent
render_expression(sum(ref(R),ref_op(_))) -->
    ["sum("], {normalize_name(R,RN)}, [RN,")"].
render_expression(avg(ref(R),ref_op(_))) -->
    ["avg("], {normalize_name(R,RN)}, [RN,")"].
render_expression(len(ref(R))) -->
    ["len("], {normalize_name(R,RN)}, [RN,")"].
render_expression(floor(ref(R))) -->
    ["floor("], {normalize_name(R,RN)}, [RN,")"].
render_expression(ceil(ref(R))) -->
    ["ceil("], {normalize_name(R,RN)}, [RN,")"].
