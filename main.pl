% Definition de l'operateur "?=".
:- op(20,xfy,?=).

% Prédicats d'affichage fournis

% set_echo: ce prédicat active l'affichage par le prédicat echo
set_echo :- assert(echo_on).

% clr_echo: ce prédicat inhibe l'affichage par le prédicat echo
clr_echo :- retractall(echo_on).

% echo(T): si le flag echo_on est positionné, echo(T) affiche le terme T
%          sinon, echo(T) réussit simplement en ne faisant rien.

echo(T) :- echo_on, !, write(T).
echo(_).

% +----------------------------------------------------------------------------+
%         ____                         _     _                     __     
%        / __ \                       | |   (_)                   /_ |  _ 
%       | |  | |  _   _    ___   ___  | |_   _    ___    _ __      | | (_)
%       | |  | | | | | |  / _ \ / __| | __| | |  / _ \  | '_ \     | |    
%       | |__| | | |_| | |  __/ \__ \ | |_  | | | (_) | | | | |    | |  _ 
%        \___\_\  \__,_|  \___| |___/  \__| |_|  \___/  |_| |_|    |_| (_)
%                                                                  
% +----------------------------------------------------------------------------+

%%regle(E, R) : Determine la regle de transformation R qui s'applique a l'equation E.
%%----- Def des conditions sur les regles -----%

/*
 * Regle rename : renvoie true si X et T sont des variables.
 * E : equation donnee.
 * R : regle rename.
 * Rename {x ?= t}∪P′;S -> P′[x/t];S[x/t]∪{x=t} si t est une variable
 */
regle(X?=T,rename) :- var(X), var(T), !.
	 
/*
 * Regle simplify : renvoie true si X est une variable et A une
 * constante.
 * E : equation donnee.
 * R : regle simplify.
 * Simplify {x ?= t}∪P′;S -> P′[x/t];S[x/t]∪{x=t} si t est une constante
 */
regle(X?=T,simplify) :- var(X), atomic(T), !.

/*
 * Regle expand : renvoie true si X est une variable, T un terme
 * compose et si X n'est pas dans T.
 * E : equation donnee.
 * R : regle expand.
 * Expand {x ?= t}∪P′;S -> P′[x/t];S[x/t]∪{x=t} si t est composé et x n’apparaît pas dans t
 */	
regle(X?=T,expand) :- var(X), compound(T), \+occur_check(X,T), !.

/*
 * Regle check : renvoie true si X et T sont differents et si X est dans
 * T.
 * E : equation donnee.
 * R : regle check.
 * Check {x?=t}∪P′;S->⊥ si x!=t et x apparaît dans t
 */	
regle(X?=T,check) :- \+X==T, occur_check(X,T), !.

/*
 * Regle orient : renvoie true si T n'est pas une variable et si X en
 * est une.
 * E : equation donnee.
 * R : regle orient.
 * Orient {t?=x}∪P′;S->{x=?t}∪P′;S si t n’est pas une variable
 */
regle(T?=X,orient) :- nonvar(T), var(X), !.

/*
 * Regle decompose : renvoie true si X et T sont des termes composes et
 * s'ils ont le meme nombre d'arguments et le meme nom.
 * E : equation donnee.
 * R : regle decompose.
 * Decompose {f(s,···,s)?=f(t,···,t)}∪P′;S->{s?=t,···,s?=t}∪P′;S
 */	
regle(X?=T,decompose) :- compound(X), compound(T), functor(X,F1,A1), functor(T,F2,A2), F1==F2, A1==A2, !.

/*
 * Regle clash : renvoie true si X et T sont des termes composes (n'ont pas le meme symbole) et
 * s'ils n'ont pas le meme nombre d'arguments.
 * E : equation donnee.
 * R : regle clash.
 * Clash {f(s,···,s)?=g(t,···,t)}∪P′;S->⊥ si f!=g ou m!=n
 */
regle(X?=T,clash) :- compound(X), compound(T), functor(X,N,A), functor(T,M,B), not( ( N==M , A==B ) ), !.

% occur_check(V,T): teste si la variable V apparait dans le terme T
occur_check(V,T) :- var(V), compound(T), arg(_,T,X), compound(X), occur_check(V,X), !;
					var(V), compound(T), arg(_,T,X), V==X, !.

% +----------------------------------------------------------------------------+
%         ____                         _     _                     ___      
%        / __ \                       | |   (_)                   |__ \   _ 
%       | |  | |  _   _    ___   ___  | |_   _    ___    _ __        ) | (_)
%       | |  | | | | | |  / _ \ / __| | __| | |  / _ \  | '_ \      / /     
%       | |__| | | |_| | |  __/ \__ \ | |_  | | | (_) | | | | |    / /_   _ 
%        \___\_\  \__,_|  \___| |___/  \__| |_|  \___/  |_| |_|   |____| (_)
%		                                                                     
% +----------------------------------------------------------------------------+
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


% +----------------------------------------------------------------------------+
%         ____                         _     _                     ____      
%        / __ \                       | |   (_)                   |___ \   _ 
%       | |  | |  _   _    ___   ___  | |_   _    ___    _ __       __) | (_)
%       | |  | | | | | |  / _ \ / __| | __| | |  / _ \  | '_ \     |__ <     
%       | |__| | | |_| | |  __/ \__ \ | |_  | | | (_) | | | | |    ___) |  _ 
%        \___\_\  \__,_|  \___| |___/  \__| |_|  \___/  |_| |_|   |____/  (_)
%		                                                                      
% +----------------------------------------------------------------------------+

%appelle unifie apres avoir desactive les affichages
%unif(P, S) :- clr_echo, unifie(P, S).

%appelle unifie apres avoir active les affichages, affiche "Yes" si on peut unifier "No" sinon (il n'y a donc pas d'echec de la procedure.
%trace_unif(P,S) :- set_echo, (unifie(P, S), echoln('Yes'), ! ;	
%		echo('No') ) .
%trace_unif(P, S) :- set_echo, unifie(P,S).
