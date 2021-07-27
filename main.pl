/*
    Trabalho Elaborado por:
    ------------------------------------------------
    2099515 - Martim Roberto Alves da Costa,
    2038217 - João Rúben Moniz Pontes,
    2038017 - Joana Sofia Teixeira Silva,
    2082117 - Rita Inês Bernardino Ribeiro Ramos,
    2038117 - Elvis Miguel Pestana Marques.
*/

/*
Predicados do Prolog utilizados:
write/1: A palavra pré-definida write é utilizada para escrever; e a
palavra not tem como função negar. writeln/1: Predicado equivalente a
"write(Termo), nl..".
read/1: read(Termo) : é o próximo termo (da linguagem Prolog) inserido
e unifica-o com "Termo".
*/

/*EXERCÍCIO 1*/

/*Operadores*/
:-op(100, fy, 'neg').
:-op(200, xfy, 'e').
:-op(300, xfy, 'ou').
:-op(400, xfy, 'imp').
:-op(1000, xfy, '==>').

/*membro/2, tal que membro(X,L) é verdadeiro se X é um elemento da lista L.*/
membro(X, [X | _]).
membro(X, [_ | Y]) :- membro(X, Y).

/*elimina/3, tal que elimina(X, L1, L2) é verdadeiro se L2 é uma lista que resulta de remover da lista L1 todos as ocurrências do elemento X.*/
elimina(_, [], []).
elimina(X, [X|Y], Z) :- elimina(X, Y, Z).
elimina(X, [Y|Z], [Y|L]) :- not(X=Y), elimina(X, Z, L).

apl_reg_aut_aux([],[]).
/*As seguintes regras referem-se à negação à direita e à esquerda.*/
apl_reg_aut_aux([X ==> Y|L], H) :- membro(neg A, X), elimina(neg A, X, X1), apl_reg_aut_aux([X1 ==> [A|Y]|L], H).
apl_reg_aut_aux([X ==> Y|L], H) :- membro(neg A, Y), elimina(neg A, Y, Y1), apl_reg_aut_aux([[A|X] ==> Y1|L], H).
/*As seguintes regras referem-se à conjunção à direita e à esquerda.*/
apl_reg_aut_aux([X ==> Y|L], H) :- membro(A e B, X), elimina(A e B, X, X1), apl_reg_aut_aux([[A,B|X1] ==> Y|L], H).
apl_reg_aut_aux([X ==> Y|L], H) :- membro(A e B, Y), elimina(A e B, Y, Y1), apl_reg_aut_aux([X ==> [A|Y1], X ==>[B|Y1]|L], H).
/*As seguintes regras referem-se  disjunção à direita e à esquerda.*/
apl_reg_aut_aux([X ==> Y|L], H) :- membro(A ou B, Y), elimina(A ou B, Y, Y1), apl_reg_aut_aux([X ==>[A, B|Y1]|L], H).
apl_reg_aut_aux([X ==> Y|L], H) :- membro(A ou B, X), elimina(A ou B, X, X1), apl_reg_aut_aux([[A|X1] ==> Y, [B|X1] ==> Y|L], H).
/*As seguintes regras referem-se à implicação à direita e à esquerda.*/
apl_reg_aut_aux([X ==> Y|L], H) :- membro(A imp B, Y), elimina(A imp B, Y, Y1), apl_reg_aut_aux([[A|X] ==> [B|Y1]|L], H).
apl_reg_aut_aux([X ==> Y|L], H) :- membro(A imp B, X), elimina(A imp B, X, X1), apl_reg_aut_aux([X1 ==> [A|Y], [B|X1] ==> Y|L], H).

apl_reg_aut_aux([X ==> Y|L], [X ==> Y|T]) :- not(membro(neg A, X)), not(membro(neg A, Y)), not(membro(A e B, X)), not(membro(A e B, Y)), not(membro(A ou B, X)), not(membro(A ou B, Y)), not(membro(A imp B, X)), not(membro(A imp B, Y)), apl_reg_aut_aux(L, T).

/*Utilizando as regras do sistema SP acima enunciadas, criou-se um predicado apl_reg_aut/1 cujo o objetivo é aplicar as regras ao sequente.*/
apl_reg_aut(S) :- apl_reg_aut_aux(S, C), write(C).

/*O predicado nao_disjunto/2 verifica se duas listas são não disjuntas.*/
nao_disjunto(L1, L2) :- membro(X, L1), membro(X, L2).
/*O predicado disjunto/2 verfica se duas listas são disjuntas.*/
disjunto(L1, L2) :- not(nao_disjunto(L1, L2)).

/*O predicado axioma/1 verifica se um sequente é axioma.*/
axioma(X ==> Y) :- nao_disjunto(X, Y).

/*O predicado todos_axiomas/1 verifica se de uma lista de sequentes todos são axiomas.*/
todos_axiomas([]).
todos_axiomas(X ==> Y) :- axioma(X ==> Y).
todos_axiomas([X ==> Y|R]) :- axioma(X ==> Y), todos_axiomas(R).

/*O predicado ant_t/1 recebe uma lista Ant e retorna a valoração adequada.*/
ant_t([]).
ant_t(Ant) :- not(is_list(Ant)), write('v(') , write(Ant), write(')=1'), nl.
ant_t([H|T]) :- ant_t(H), ant_t(T).

/*O predicado con_f/1 recebe uma lista Con e retorna a valoração adequada.*/
con_f([]).
con_f(Con) :- not(is_list(Con)), write('v(') , write(Con), write(')=0'), nl.
con_f([H|T]) :- con_f(H), con_f(T).

/*O predicado v_aux/1 recebe um sequente e aplica os predicados acima definidos.*/
v_aux(X ==> Y) :- list_to_set(X,XS), list_to_set(Y, YS), ant_t(XS), con_f(YS).

/*O predicado valoracao/1 recebe uma lista de sequentes e verifica a sua valoração.*/
valoracao([]).
valoracao([X ==> Y | _]) :- not(axioma(X==>Y)) , v_aux(X ==> Y).
valoracao([X ==> Y | T]) :- axioma(X==>Y) , valoracao(T).

/*O predicado teorema/1 verifica se o sequente é teorema ou não, e se não for retorna um exemplo de uma valoração que o falsifique.*/
teorema(S) :- apl_reg_aut_aux(S, C), todos_axiomas(C), nl, write('Este sequente é um teorema do sistema de sequentes.').
teorema(S) :- apl_reg_aut_aux(S, C), not(todos_axiomas(C)), nl, write('Este sequente não é um teorema do sistema de sequentes, e um exemplo de uma valoração que o falsifique é:'), nl, nl,valoracao(C), nl.

/*EXERCÍCIO 2*/

apl_reg_aut_aux_2([],[]).
/*As seguintes regras referem-se à negação à direita e à esquerda.*/
apl_reg_aut_aux_2([X ==> Y|L], H) :- membro(neg A, X), elimina(neg A, X, X1),write('R neg, e --> '), write([X1 ==> [A|Y]|L]), nl,nl, apl_reg_aut_aux_2([X1 ==> [A|Y]|L], H).
apl_reg_aut_aux_2([X ==> Y|L], H) :- membro(neg A, Y), elimina(neg A, Y, Y1), write('R neg, d --> '), write([[A|X] ==> Y1|L]), nl,nl, apl_reg_aut_aux_2([[A|X] ==> Y1|L], H).
/*As seguintes regras referem-se à conjunção à direita e à esquerda.*/
apl_reg_aut_aux_2([X ==> Y|L], H) :- membro(A e B, X), elimina(A e B, X, X1), write('R e, e --> '), write([[A,B|X1] ==> Y|L]), nl,nl, apl_reg_aut_aux_2([[A,B|X1] ==> Y|L], H).
apl_reg_aut_aux_2([X ==> Y|L], H) :- membro(A e B, Y), elimina(A e B, Y, Y1),write('R e, d --> '), write([X ==> [A|Y1], X ==>[B|Y1]|L]), nl,nl, apl_reg_aut_aux_2([X ==> [A|Y1], X ==>[B|Y1]|L], H).
/*As seguintes regras referem-se à disjunção à direita e à esquerda.*/
apl_reg_aut_aux_2([X ==> Y|L], H) :- membro(A ou B, Y), elimina(A ou B, Y, Y1),write('R ou, d --> '), write([X ==>[A, B|Y1]|L]), nl,nl, apl_reg_aut_aux_2([X ==>[A, B|Y1]|L], H).
apl_reg_aut_aux_2([X ==> Y|L], H) :- membro(A ou B, X), elimina(A ou B, X, X1), write('R ou, e --> '), write([[A|X1] ==> Y, [B|X1] ==> Y|L]), nl,nl, apl_reg_aut_aux_2([[A|X1] ==> Y, [B|X1] ==> Y|L], H).
/*As seguintes regras referem-se à implicação à direita e à esquerda.*/
apl_reg_aut_aux_2([X ==> Y|L], H) :- membro(A imp B, Y), elimina(A imp B, Y, Y1), write('R imp, d --> '), write([[A|X] ==> [B|Y1]|L]), nl,nl, apl_reg_aut_aux_2([[A|X] ==> [B|Y1]|L], H).
apl_reg_aut_aux_2([X ==> Y|L], H) :- membro(A imp B, X), elimina(A imp B, X, X1), write('R imp, e --> '),write([X1 ==> [A|Y], [B|X1] ==> Y|L]), nl,nl, apl_reg_aut_aux_2([X1 ==> [A|Y], [B|X1] ==> Y|L], H).

apl_reg_aut_aux_2([X ==> Y|L], [X ==> Y|T]) :- not(membro(neg A, X)), not(membro(neg A, Y)), not(membro(A e B, X)), not(membro(A e B, Y)), not(membro(A ou B, X)), not(membro(A ou B, Y)), not(membro(A imp B, X)), not(membro(A imp B, Y)), apl_reg_aut_aux_2(L, T).

/*O predicado apl_reg_aut_2/1 aplica as regras a um sequente e tem como objetivo descrever a construção de uma árvore de dedução.*/
apl_reg_aut_2(S) :- nl,apl_reg_aut_aux_2(S, C).


/*EXERCÍCIO 3*/


/*Regras do sistema SP nomeadamente, a negação, conjunção, implicação e disjunção, tanto à direita como à esquerda que serão utilizadas como auxiliares no processo de construção de uma árvore esgotada.*/
rneg_e([X ==> Y], Folhas, Novas_Folhas) :-
    membro(neg A, X),
    elimina(neg A, X, X1),
    elimina([X ==> Y], Folhas, H1),
    append([[X1 ==> [A|Y]]], H1, H2),
    elimina([], H2, Novas_Folhas).

rneg_d([X ==> Y], Folhas, Novas_Folhas) :-
    membro(neg A, Y),
    elimina(neg A, Y, Y1),
    elimina([X ==> Y], Folhas, H1),
    append([[[A|X] ==> Y1]], H1, H2),
    elimina([], H2, Novas_Folhas).

re_e([X ==> Y], Folhas, Novas_Folhas) :-
    membro(A e B, X),
    elimina(A e B, X, X1),
    elimina([X ==> Y], Folhas, H1),
    append([[[A,B|X1] ==> Y]], H1, H2),
    elimina([], H2, Novas_Folhas).

re_d([X ==> Y], Folhas, Novas_Folhas) :-
    membro(A e B, Y),
    elimina(A e B, Y, Y1),
    elimina([X ==> Y], Folhas, H1),
    append([[X ==> [A|Y1]], [X ==>[B|Y1]]], H1, H2),
    elimina([], H2, Novas_Folhas).

rimp_d([X ==> Y], Folhas, Novas_Folhas) :-
    membro(A imp B, Y),
    elimina(A imp B, Y, Y1),
    elimina([X ==> Y], Folhas, H1),
    append([[[A|X] ==> [B|Y1]]], H1, H2),
    elimina([], H2, Novas_Folhas).

rimp_e([X ==> Y], Folhas, Novas_Folhas) :-
    membro(A imp B, X),
    elimina(A imp B, X, X1),
    elimina([X ==> Y], Folhas, H1),
    append([[X1 ==> [A|Y]], [[B|X1] ==> Y]], H1, H2),
    elimina([], H2, Novas_Folhas).

rou_d([X ==> Y], Folhas, Novas_Folhas) :-
    membro(A ou B, Y),
    elimina(A ou B, Y, Y1),
    elimina([X ==> Y], Folhas, H1),
    append([[X ==>[A, B|Y1]]], H1, H2),
    elimina([], H2, Novas_Folhas).

rou_e([X ==> Y], Folhas, Novas_Folhas) :-
    membro(A ou B, X),
    elimina(A ou B, X, X1),
    elimina([X ==> Y], Folhas, H1),
    append([[[A|X1] ==> Y], [[B|X1] ==> Y]], H1, H2),
    elimina([], H2, Novas_Folhas).

/*Aplicação das regras acima definidas.*/
apl_reg(rneg_e, S, Folhas, Novas_Folhas):- rneg_e(S, Folhas, Novas_Folhas).
apl_reg(rneg_d, S, Folhas, Novas_Folhas):- rneg_d(S, Folhas, Novas_Folhas).
apl_reg(rimp_e, S, Folhas, Novas_Folhas):- rimp_e(S, Folhas, Novas_Folhas).
apl_reg(rimp_d, S, Folhas, Novas_Folhas):- rimp_d(S, Folhas, Novas_Folhas).
apl_reg(re_e, S, Folhas, Novas_Folhas):- re_e(S, Folhas, Novas_Folhas).
apl_reg(re_d, S, Folhas, Novas_Folhas):- re_d(S, Folhas, Novas_Folhas).
apl_reg(rou_e, S, Folhas, Novas_Folhas):- rou_e(S, Folhas, Novas_Folhas).
apl_reg(rou_d, S, Folhas, Novas_Folhas):- rou_d(S, Folhas, Novas_Folhas).

/*tem_conectivos/1 : Dado um sequente X ==> Y, este predicado verifica se X ou Y contém algum conectivo.*/
tem_conectivos(X ==> Y) :- membro(neg _, X).
tem_conectivos(X ==> Y) :- membro(neg _, Y).
tem_conectivos(X ==> Y) :- membro(_ e _, X).
tem_conectivos(X ==> Y) :- membro(_ e _, Y).
tem_conectivos(X ==> Y) :- membro(_ ou _, X).
tem_conectivos(X ==> Y) :- membro(_ ou _, Y).
tem_conectivos(X ==> Y) :- membro(_ imp _, X).
tem_conectivos(X ==> Y) :- membro(_ imp _, Y).

/*arv_esgotada/1 : Verifica se todas as folhas são axiomas ou não tem conectivos.*/
arv_esgotada([]).
arv_esgotada([[X ==> Y]|R]) :- axioma(X ==> Y), arv_esgotada(R).
arv_esgotada([[X ==> Y]|R]) :- not(tem_conectivos(X ==> Y)), arv_esgotada(R).

/*enesimo/3 : tal que enesimo(N, L, X) tem o valor verdadeiro se o elemento X está na posição N da lista L.*/
enesimo(1,[X|L],X).
enesimo(N,[X|L],Y):-enesimo(N1,L,Y), N is N1+1.

/*escrever_folhas/2 : Lista as folhas e as suas posições correspondentes para facilitar a seleção ao utilizador.*/
escrever_folhas([], Folhas).
escrever_folhas([H|T], Folhas):-
    enesimo(N, Folhas, H),
    write(N),
    write(" : "),
    writeln(H),
    escrever_folhas(T, Folhas).

/*aux_ajuda/1 : Predicado auxiliar usado pelo ajuda_sp, cujo objetivo é a demonstração das folhas atuais da árvore, escolha da folha a qual aplicar a regra.*/
aux_ajuda(Folhas) :-
    arv_esgotada(Folhas),
    writeln("As folhas neste momento são:"),
    escrever_folhas(Folhas, Folhas),
    writeln("Árvore esgotada. Execução terminada!").
aux_ajuda(Folhas) :-
    not(arv_esgotada(Folhas)),
    writeln("As folhas neste momento são:"),
    escrever_folhas(Folhas, Folhas),
    writeln("Escreva o número correspondente à  folha a que deseja aplicar a regra."),
    read(N_escolhida),
    enesimo(N_escolhida, Folhas, F_escolhida),
    write("Folha selecionada:"),
    writeln(F_escolhida),
    writeln("Escreva a regra que pretende aplicar (rneg_e, rneg_d, rimp_e, rimp_d, re_e, re_d, rou_e, rou_d):"),
    read(Regra),
    apl_reg(Regra, F_escolhida, Folhas, Novas_Folhas),
    aux_ajuda(Novas_Folhas).

/*ajuda_sp/0 : Recebe um sequente e inicia o processo de construção da árvore.*/
ajuda_sp :-
    writeln('Redija o sequente que pretende analisar:'),
    read(Sequente),
    aux_ajuda([Sequente]).
