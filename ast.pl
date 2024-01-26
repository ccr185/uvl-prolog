:- module(ast, []).
:- set_prolog_flag(double_quotes, string).
:- set_portray_text(enabled, true).
:- use_module(library(dcg/high_order)).
:- use_module(library(portray_text)).
:- use_module(library(apply)).
:- use_module(library(apply_macros)).
:- use_module(library(yall)).
:- use_module(uvl).

print_clif_from_ast(File) :-
    parse(File, AST, []),
    print_term(AST,[]),
    clif_from_ast(CLIF, AST),
    print_term(CLIF, []).



clif_from_ast(CLIF, AST) :-
    phrase(ast_gen(AST), CLIF).

ast_gen(
    ast(header(namespace(N),includes(In),imports(Im)),Features,Constraints)
) -->
      feature_sentences(Features),
      constraint_sentences(Constraints).

feature_sentences(nil) --> [].
feature_sentences([]) --> [].
feature_sentences([Feature|Fs]) -->
    feature_sentence(Feature),
    feature_sentences(Fs).

feature_sentence(
    feature(
        name(N), type(FeatureType), cardinality(Card),
        attributes(Attrs), group(Gs)
    )
) -->
    feature_var_decl(FeatureType, N, Card),
    %%% Here we would handle the attrs
    feature_group_sentences(Gs, N).


feature_var_decl(boolean, N, _) --> ["(bool ", N, " )"].
feature_var_decl(integer, N, nil) --> ["(int ", N, " )"].
feature_var_decl(integer, N, card(From,To)) --> ["(int (", From, " ", To, ") ", N, " )"].
feature_var_decl(string, _, _).
feature_var_decl(real, _, _).

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
    feature_sentences(Fs).
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
    feature_sentences(Fs).

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
        )
    },
    ["(= ",N, " ", FeatName, " )"],
    feature_sentence(F),
    mandatory_group_sentence(Fs, N).

optional_group_sentence([],_) --> [].
optional_group_sentence([F|Fs], N) -->
    {feature_name(F,FName)},
    ["(>= ", N, " ", FName, ")"],
    feature_sentence(F),
    optional_group_sentence(Fs,N).

%% Utility
feature_name(feature(name(N),_,_,_,_),N).
feature_type(feature(_,type(T),_,_,_),T).
feature_card(feature(_,_,cardinality(Card),_,_),Card).
feature_attr(feature(_,_,_,attributes(Attrs),_),Attrs).
feature_group(feature(_,_,_,_,group(FeatGroups)), FeatGroups).

%% Constraints
constraint_sentences([]) --> [].
constraint_sentences([C|Cs]) -->
    constraint_sentence(C),
    constraint_sentences(Cs).

constraint_sentence(equation(E)) --> render_equation(E).
constraint_sentence(literal_constraint(C)) --> [C].
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
