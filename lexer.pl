:- module(lexer, [lex_uvl/2]).
:- set_prolog_flag(double_quotes, string).
:- set_prolog_flag(encoding, utf8).
:- encoding(utf8).
:- use_module(library(dcg/basics)).
:- use_module(library(dcg/high_order)).
:- use_module(library(pio)).
%:- use_module(library(regex)).
:- use_module(library(pcre)).
:- use_module(library(clpfd)).
:- use_module(library(lists)).
:- use_module(library(yall)).
:- use_module(library(apply)).
:- use_module(library(apply_macros)).
:- use_module(library(portray_text)).

%% Main entrypoint for the Lexer
%% defines lex_uvl(-Tokens,+File) that, given a
%% Filename, transforms the raw string intro a token list
%% for further parsing
lex_uvl(Tokens, File) :-
    phrase_from_file(tokenize(TokensCollected), File),
    flatten(TokensCollected, Tokens).

tokenize(Tokens) -->
    tokenize_([0],Tokens).

%% FIXME: This definition and the one at the bottom seem to conflict.
tokenize_(RemainingIndentStack, DedentTokens) --> eos, !,
    {
        format("Remaining Indent Stack: ~w", [RemainingIndentStack]),
        length(RemainingIndentStack, Length),
        dedentStack(Length, RemainingIndentStack, DedentTokens)
    }.
tokenize_([IndentLevel|Is], [LineToks|Tokens]) -->
    tokenize_line(LineIndent, LineToks0), !,
    {
        % Check for equal indent level
        (
            LineIndent =:= IndentLevel
        ) -> (
            % Case 1: Indentation level is the same
            % do not generate indent/dedent token
            LineToks = LineToks0,
            IndentStack = [IndentLevel|Is]
        ) ; (
            % Check for increase/decrease in indent
            % level
            (
                LineIndent #> IndentLevel
            ) -> (
                % Case 2: Indentation is higher than stack,
                % emit an indent token before the line tokens
                LineToks = [indent | LineToks0],
                IndentStack = [LineIndent,IndentLevel|Is],
                writeln("emit indent token")
            ) ; (
                % Case 3: Indentation is lower than stack
                % check that this level exists
                % emit a dedent token
                % TODO: Add error checking and throw an error if
                % there's a problem.
                member(LineIndent, Is),
                drop_higher(Is, LineIndent, NewStack, NPopped0),
                %Since we are 0 indexing and we are
                %dropping with the last indent already removed
                %we always drop N+1
                NPopped #= NPopped0 + 1,
                length(Dedents, NPopped),
                maplist([X]>>(X = dedent), Dedents),
                append(Dedents, LineToks0, LineToks),
                %LineToks = [dedent | LineToks0],
                IndentStack = NewStack,
                format("emit ~w dedent tokens \n", [NPopped])
            )
        )
    },
    tokenize_(IndentStack, Tokens).
% TODO: emit dedent tokens corresponding
% to the remaining indent level left on stack
tokenize_(RemainingIndentStack, DedentTokens) -->
    [], !,
    {
        format("Remaining Indent Stack: ~w", [RemainingIndentStack]),
        length(RemainingIndentStack, Length),
        dedentStack(Length, RemainingIndentStack, DedentTokens)
    }.

%We are certain that the element is in the list.
drop_higher(OrigStack, Elem, NewStack, Pos) :-
    nth0(Pos,OrigStack, Elem),
    drop(Pos, OrigStack, NewStack), !.

%Based on https://www.swi-prolog.org/pldoc/doc/_SWI_/library/dialect/hprolog.pl
drop(0, LastElements, LastElements) :- !.
drop(N, [_|Tail], LastElements) :-
    N #> 0, N1 #= N- 1, drop(N1,Tail,LastElements).

dedentStack(1, _, []) :- !.
dedentStack(N, [_|TA], [dedent|TB]) :-
    N #> 0, N2 #= N - 1,
    dedentStack(N2, TA, TB).

tokenize_line(N, Ts) -->
    indent(N),
    line_tokens(Ts).
    %(`\n`|`\r\n`).

indent(N) --> indent_(0,N).

indent_(N0,N) --> ` `,  !, indent_(N1,N), {N1 #= N0 + 1}.
indent_(N0,N) --> `\t`, !, indent_(N1,N), {N1 #= N0 + (8 - (N0 mod 8))}.
indent_(N0,N0) --> [], !.

line_tokens([]) --> eol, !.
line_tokens([T|Ts]) -->
    next_token(T), !, whites, line_tokens(Ts).
line_tokens([]) --> [], !.

next_token(Token) -->
    (keyword(Token), !, {format("read keyword ~w \n", [Token])}) |
    (double_char(Token), !, {format("read double_char ~w \n", [Token])}) |
    (single_char(Token), !, {format("read single_char ~w \n", [Token])}) |
    (literal(Token), !, {format("read literal ~w \n", [Token])}).

% Keywords
keyword(Token) -->
    ("group-cardinality", {Token = group_card}, !) |
    ("feature-cardinality", {Token = feature_card}, !) |
    ("aggregate-function", {Token = agg_fun}, !) |
    ("string-constraints", {Token = string_constraints}, !) |
    ("namespace", {Token = namespace}, !) |
    ("include", {Token = include}, !) |
    ("imports", {Token = imports}, !) |
    ("features", {Token = features}, !) |
    ("as", {Token = as}, !) |
    ("or", {Token = or_group}, !) |
    ("alternative", {Token = alternative}, !) |
    ("optional", {Token = optional}, !) |
    ("mandatory", {Token = mandatory}, !) |
    ("cardinality", {Token = cardinality}, !) |
    ("constraints", {Token = constraints}, !) |
    ("constraint", {Token = constraint}, !) |
    ("sum", {Token = sum}, !) |
    ("avg", {Token = avg}, !) |
    ("len", {Token = len}, !) |
    ("floor", {Token = floor}, !) |
    ("ceil", {Token} = ceil, !) |
    ("String", {Token = string_t}, !) |
    ("Integer", {Token = integer_t}, !) |
    ("Real", {Token = real_t}, !) |
    ("Boolean", {Token = boolean_t}, !) |
    ("Arithmetic", {Token = arithmetic_t}, !) |
    ("Type", {Token = type_t}, !) |
    ("true", {Token = lit_true}, !) |
    ("false", {Token = lit_false}, !).

%Double Char Toks
double_char(Token) -->
    ("..", {Token = range}, !) |
    ("<=>", {Token = equivalence}, !) |
    ("=>", {Token = impl}, !) |
    ("==", {Token = equal}, !) |
    ("<=", {Token = lte}, !) |
    (">=", {Token = gte}, !) |
    ("!=", {Token = neq}, !) |
    ("//", {Token = comment_start}, !) |
    ("/*", {Token = ml_comment_start}, !) |
    ("*/", {Token = ml_comment_end}, !).

single_char(Token) -->
    (`,`, {Token = comma}, !) |
    (`.`, {Token = dot}, !) |
    (`!`, {Token = not}, !) |
    (`&`, {Token = and}, ! ) |
    (`|`, {Token = or}, !) |
    (`<`, {Token = lt}, !) |
    (`>`, {Token = gt}, !) |
    (`*`, {Token = mul}, !) |
    (`+`, {Token = add}, !) |
    (`-`, {Token = sub}, !) |
    (`/`, {Token = div}, !) |
    ("(", {Token = lparen}, !) |
    (")", {Token = rparen}, !) |
    ("[", {Token = lbracket}, !) |
    ("]", {Token = rbracket}, !) |
    ("{", {Token = lbrace}, ! ) |
    ("}", {Token = rbrace}, !).

literal(float(Token)) --> float(Token), !.
literal(integer(Token)) --> integer(Token), !.
literal(Token) -->
    string_without(".,-(){}[] \t\n\r", Codes),
    {
        \+ length(Codes, 0),
        atom_codes(Atom, Codes),
        atom_string(Atom, Str),
        (
            id_strict(Str)
        ) -> (
            Token = id_strict(Str)
        ) ; (
            (
                id_not_strict(Str)
            ) -> (
                Token = id_not_strict(Str)
            ) ; (
                (
                    normal_string(Str)
                ) -> (
                    Token = normal_string(Str)
                ) ; (
                    throw("Unrecognized string format")
                )
            )
        )
    }, !.

id_strict(Str) :-
    re_match(
        "^[a-zA-Z]([a-zA-Z0-9_]|#|§|%|\\|\\?|\'|ä|ü|ö|ß|;)*(?![\\)\\]\\}])$",
        Str,[anchored(true),utf(true)]
    ).
id_not_strict(Str) :- re_match("\"[^\r\n\".]+\"$", Str, [anchored(true),utf(true)]).
normal_string(Str) :- re_match("\'[^\r\n\'.]+\'$", Str, [anchored(true),utf(true)]).%% %

%id_strict(Str) :- Str =~ '[a-zA-Z]([a-zA-Z0-9_]|#|§|%|\\?|\\|\'|ä|ü|ö|ß|;)*(?![\)\]\}])$', !.
%id_not_strict(Str) :- Str =~ '\"[^\r\n\".]+\"$', !.
%normal_string(Str) :- Str =~  '\'[^\r\n\'.]+\'$', !.
