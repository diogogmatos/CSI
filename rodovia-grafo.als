sig Estrada {
    id: one String, -- identificador único da estrada
    intercecoes: seq Intercecao,
}

sig Segmento {
    inicio: one Intercecao,
    fim: one Intercecao,
    regras: set Regra, -- regras em vigor ao longo do segmento
    subSegmentos: lone SubSegmento -- cabeça da lista ligada de subsegmentos
}

sig SubSegmento {
    elemento: one Sinal + Obstaculo,
    proxSubSegmento: lone SubSegmento
}

abstract sig Regra {}

sig Prioridade extends Regra {}

pred regrasBase {
    // Uma estrada tem pelo menos 2 interceções
    all e: Estrada | #e.intercecoes > 1
    // Todas as interseções que compõe uma estrada são únicas
    all e: Estrada | all idx1, idx2: e.intercecoes.inds | idx1 != idx2 implies e.intercecoes[idx1] != e.intercecoes[idx2]
    // O início e o fim de um segmento são distintos
    all s: Segmento | s.inicio != s.fim
    // Todos os segmentos são únicos
    all s1, s2: Segmento | s1 != s2 implies s1.inicio != s2.inicio or s1.fim != s2.fim
    // Cada par sequencial de interceções de uma estrada deve estar conectado por um segmento
    all e: Estrada | all idx: e.intercecoes.inds | 
        let nextIdx = add[idx, 1] | 
        nextIdx in e.intercecoes.inds implies
        (one s: Segmento | s.inicio = e.intercecoes[idx] and s.fim = e.intercecoes[nextIdx])
    // Não existe segmentos com sentido inverso
    all s1, s2: Segmento | 
        s1 != s2 implies not (s1.inicio = s2.fim and s1.fim = s2.inicio)
    // Não existem subsegmentos soltos
    all s: SubSegmento | 
        s in SubSegmento.proxSubSegmento or s in Segmento.subSegmentos
    // Não existem obstáculos soltos
    all o: Obstaculo | o in SubSegmento.elemento
    // Não existem sinais soltos
    all s: Sinal | s in SubSegmento.elemento
    // Não existem regras soltas
    all r: Regra | r in Segmento.regras
    // Não existem ciclos de subsegmentos
    all s: SubSegmento | s not in s.^proxSubSegmento
    all c: Cruzamento | (#inicio.c) = (#fim.c) and #inicio.c = 2
    all e: Entroncamento | (#inicio.e = 1 and #fim.e = 2) or (#inicio.e = 2 and #fim.e = 1)
    // So pode existir no maximo um instacia de cada tipo de regra por segmento
    all s: Segmento | (lone r: s.regras | r in Prioridade)
    // Subsegmentos não devem ser partilhados entre segmentos
    all s1, s2: Segmento | s1 != s2 implies
        no s1.subSegmentos.*proxSubSegmento & s2.subSegmentos.*proxSubSegmento
    // Sinais nao devem ser partilhados entre subsegmentos
    all s1, s2: SubSegmento | s1 != s2 implies
        no s1.elemento & s2.elemento
} 

// Interseções

abstract sig Intercecao {}

sig Rotunda extends Intercecao {}
sig Entroncamento extends Intercecao {}
sig Cruzamento extends Intercecao {}

// Obstáculos

abstract sig Obstaculo {}

sig Passadeira extends Obstaculo {}
sig Lomba extends Obstaculo {}
sig Depressao extends Obstaculo {}
sig Tunel extends Obstaculo {}

// Sinais

abstract sig Sinal {}

// Sinais de Perigo

abstract sig Perigo extends Sinal {}

sig PerigoLomba extends Perigo {}
sig PerigoDepressao extends Perigo {}
sig PerigoLombaOuDepressao extends Perigo {}
sig PerigoPassadeira extends Perigo {}
sig PerigoTunel extends Perigo {}

// Sinais de Regulamentação

abstract sig Regulamentacao extends Sinal {}

// -- Sinais de Cedência de Passagem

abstract sig Cedencia extends Regulamentacao {}

sig CedenciaPassagem extends Cedencia {}
sig CedenciaStop extends Cedencia {}
sig CedenciaRotunda extends Cedencia {}
sig CedenciaCruzamento extends Cedencia {}
sig CedenciaEntroncamento extends Cedencia {}

// -- Sinais de Proibição

abstract sig Proibicao extends Regulamentacao {}

sig ProibicaoVelocidadeMaxima extends Proibicao {}
sig ProibicaoUltrapassagem extends Proibicao {}
sig ProibicaoUltrapassagemPesados extends Proibicao {}
sig ProibicaoUltrapassagemMotociclos extends Proibicao {}

sig ProibicaoFim extends Proibicao {}
sig ProibicaoFimVelocidadeMaxima extends Proibicao {}
sig ProibicaoFimUltrapassagem extends Proibicao {}
sig ProibicaoFimUltrapassagemPesados extends Proibicao {}
sig ProibicaoFimUltrapassagemMotociclos extends Proibicao {}

// -- Sinais de Obrigação

abstract sig Obrigacao extends Regulamentacao {}

sig ObrigacaoRotunda extends Obrigacao {}

// -- Sinais de Informação

abstract sig Informacao extends Sinal {}

sig InformacaoPassadeira extends Informacao {}

// Regras de Trânsito

// -- Regras Sinais de Perigo

pred regraPerigo[sinal: set Perigo, obstaculo: set Obstaculo] {
    all s: Segmento, sub: s.subSegmentos.*proxSubSegmento |
        sub.elemento in obstaculo implies
            one prev: *(~proxSubSegmento)[sub] | prev.elemento in sinal
}

pred regrasPerigo {
    regraPerigo[PerigoLomba + PerigoLombaOuDepressao, Lomba] and
    regraPerigo[PerigoDepressao + PerigoLombaOuDepressao, Depressao] and
    regraPerigo[PerigoPassadeira, Passadeira] and
    regraPerigo[PerigoTunel, Tunel]
}

// -- Regras Sinais de Cedência

pred regraCedenciaPassagem {
    all s1: Segmento | 
        s1.fim in Cruzamento + Entroncamento and
        (some s2: Segmento | s2 != s1 and s2.fim = s1.fim and some r: s2.regras | r in Prioridade)
    implies
        one ss: s1.subSegmentos.*proxSubSegmento | 
            ss.elemento in CedenciaPassagem or ss.elemento in CedenciaStop
}

pred regraCedenciaCruzamento {
    all s: Segmento | (s.fim in Cruzamento and some r: s.regras | r in Prioridade)
    iff
        one ss: s.subSegmentos.*proxSubSegmento | ss.elemento in CedenciaCruzamento
}

pred regraCedenciaEntroncamento {
    all s: Segmento | (s.fim in Entroncamento and some r: s.regras | r in Prioridade)
    iff
        one ss: s.subSegmentos.*proxSubSegmento | ss.elemento in CedenciaEntroncamento
}

pred regraCedenciaRotunda {
    all s: Segmento | s.fim in Rotunda iff
        one ss: s.subSegmentos.*proxSubSegmento | ss.elemento in CedenciaRotunda
}

// -- Regras Sinais Proibição

pred regraInformaProibicao {
    all s1: Segmento | 
        s1.inicio in Cruzamento + Entroncamento and
        (some s2: Segmento | s2 != s1 and s2.fim = s1.inicio and
        // Ambos os segmentos pertencem à mesma estrada (as interseções que os compõe pertencem à mesma estrada)
        (some e: Estrada, idx1, idx2, idx3: e.intercecoes.inds
            | e.intercecoes[idx1] = s2.inicio and e.intercecoes[idx2] = s2.fim and e.intercecoes[idx3] = s1.fim) and
        // O segmento anterior (s2) tem um limite de velocidade
        some ss: s2.subSegmentos.*proxSubSegmento | ss.elemento in ProibicaoVelocidadeMaxima)
    implies
        one ss1: s1.subSegmentos.*proxSubSegmento | 
            ss1.elemento in ProibicaoVelocidadeMaxima or ss1.elemento in ProibicaoFim or ss1.elemento in ProibicaoFimVelocidadeMaxima
}

// Encontrar modelos válidos
run {
    some Estrada
    regrasBase
    regrasPerigo
    regraCedenciaRotunda
    regraCedenciaPassagem
    regraCedenciaCruzamento
    regraCedenciaEntroncamento
    regraInformaProibicao

    // some s: Segmento | s.fim in Cruzamento and some r: s.regras | r in Prioridade

    // Novo predicado: existe um segmento que começa nos índices 0 e 1 de uma estrada e tem um sinal de ProibicaoVelocidadeMaxima
    // some e: Estrada | 
    //     let i0 = e.intercecoes[0], i1 = e.intercecoes[1] |
    //         some s: Segmento | 
    //             s.inicio = i0 and s.fim = i1 and 
    //             some ss: s.subSegmentos.*proxSubSegmento | ss.elemento in ProibicaoVelocidadeMaxima
} for 10 Estrada, 10 Segmento, 10 SubSegmento, 10 Regra, 10 Intercecao, 10 Obstaculo, 10 Sinal, exactly 10 String

// Encontrar modelos inválidos
check {}

run {
    some Estrada
    #Rotunda = 0
} for 10 Estrada, 10 Segmento, 10 SubSegmento, 10 Regra, 10 Intercecao, 10 Obstaculo, 10 Sinal, exactly 10 String