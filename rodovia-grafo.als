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
sig VelocidadeMaxima extends Regra {}

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
    
    all c: Cruzamento | (#inicio.c) = (#fim.c) and #inicio.c = 2
    all e: Entroncamento | (#inicio.e = 1 and #fim.e = 2) or (#inicio.e = 2 and #fim.e = 1)
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

// -- Regras Sinais de Cedência

// Encontrar modelos válidos
run {
    some Estrada
    some Segmento
    regrasBase
} for 10 Estrada, 10 Segmento, 10 SubSegmento, 10 Regra, 10 Intercecao, 10 Obstaculo, 10 Sinal, exactly 10 String

// Encontrar modelos inválidos
check {}
