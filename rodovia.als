// Utils

enum Bool { True, False }

// Main Code

sig Universo {
    estradas: set Estrada,
}

sig Estrada {
    id: one String, -- identificador única da estrada
    inicio: one Segmento, -- cabeça da lista ligada de segmentos que compõe a estrada
}

sig Segmento {
    inter: lone Intercecao, -- delimita o começo do segmento
    regras: set Regulamentacao, -- regras do segmento atual e as herdadas do segmento anterior (se existir) ??
    proxSegmento: lone Segmento, -- próximo segmento na lista
    subSegmentos: lone SubSegmento -- cabeça da lista ligada de subsegmentos
}

sig SubSegmento {
    elemento: one Sinal + Obstaculo, 
    proxSubSegmento: lone SubSegmento
}

fact {
    // Uma estrada deve ter um identificador único
    all e1, e2: Estrada | e1.id = e2.id implies e1 = e2
    // O início da estrada deve ser um segmento único
    all e1, e2: Estrada | e1.inicio = e2.inicio implies e1 = e2
    // O próximo segmento de um segmento não pode ser ele próprio
    all s: Segmento | s.proxSegmento != s
    // O próximo subsegmento de um subsegmento não pode ser ele próprio
    all ss: SubSegmento | ss.proxSubSegmento != ss
    // Todos os segmentos de uma estrada devem ser únicos
    all e: Estrada | all s1, s2: e.inicio + e.inicio.*proxSegmento | s1 != s2 implies s1 not in s2.*proxSegmento
    // Todos os subsegmentos de um segmento devem ser únicos
    all s: Segmento, ss1, ss2: s.subSegmentos + s.subSegmentos.*proxSubSegmento | ss1 != ss2
    // Estradas diferentes não têm segmentos em comum
    all e1, e2: Estrada | e1 != e2 implies no e1.inicio + e1.inicio.*proxSegmento & e2.inicio + e2.inicio.*proxSegmento
    // Segmentos não partilham subsegmentos
    all s1, s2: Segmento | s1 != s2 implies no s1.subSegmentos + s1.subSegmentos.*proxSubSegmento & s2.subSegmentos + s2.subSegmentos.*proxSubSegmento
    // Estradas diferentes não têm subsegmentos em comum
    all e1, e2: Estrada | e1 != e2 implies no e1.inicio.subSegmentos + e1.inicio.subSegmentos.*proxSubSegmento & e2.inicio.subSegmentos + e2.inicio.subSegmentos.*proxSubSegmento
}

// As estradas dos cruzamentos e entroncamentos nao podem ambas ter prioridade
fact {
    all s1, s2: Segmento |
    s1.inter in Cruzamento + Entroncamento and
    s2.inter in Cruzamento + Entroncamento and
    s1.inter.id = s2.inter.id implies
        // Ou uma tem prioridade e a outra não
        (s1.inter in Entroncamento and s1.inter.(Entroncamento <: comPrioridade) = True and
         s2.inter in Entroncamento and s2.inter.(Entroncamento <: comPrioridade) = False) or
        // Ou ambas não têm prioridade
        (s1.inter in Entroncamento and s1.inter.(Entroncamento <: comPrioridade) = False and
         s2.inter in Entroncamento and s2.inter.(Entroncamento <: comPrioridade) = False) or
         // Ou uma tem prioridade e a outra não
        (s1.inter in Cruzamento and s1.inter.(Cruzamento <: comPrioridade) = True and
         s2.inter in Cruzamento and s2.inter.(Cruzamento <: comPrioridade) = False) or
         // Ou ambas não têm prioridade
        (s1.inter in Cruzamento and s1.inter.(Cruzamento <: comPrioridade) = False and
         s2.inter in Cruzamento and s2.inter.(Cruzamento <: comPrioridade) = False)
}

// estrada1: S1 -> S2 -> S3 -> ... -> Sn
// estrada2: S1 -> S2 -> S3 -> ... -> Sn

// Rotunda -------------------------------------------------------------------------------------- Cruzamento

// Rotunda ---- Sinal de Lomba --- Limite Velocidade --- Lomba ---- Rotunda

// Rotunda -- Velocidade Maxima -- Aviso Rotunda -- Rotunda ------ Fim Velocidade Maxima ------- Cruzamento

abstract sig Elemento {}

// Interseções

abstract sig Intercecao extends Elemento {
    id: one String -- identificador único da interseção
}

sig Rotunda extends Intercecao {}
sig Entroncamento extends Intercecao {
    comPrioridade: one Bool,
}
sig Cruzamento extends Intercecao {
    comPrioridade: one Bool,
}

// Obstáculos

abstract sig Obstaculo extends Elemento {}

sig Passadeira extends Obstaculo {}
sig Lomba extends Obstaculo {}
sig Depressao extends Obstaculo {}
sig Tunel extends Obstaculo {}

// Sinais

abstract sig Sinal extends Elemento {}

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

// s.proxSegmento -- próximo
// s.*proxSegmento -- todos os próximos
// *(~proxSegmento)[s] -- todos os anteriores
// ~proxSegmento[s] -- imediatamente anterior

// -- Regras Sinais de Perigo

pred regraPerigo[sinal: set Perigo, obstaculo: set Obstaculo] {
    // Antes de um obstaculo deve existir uma sinalização de perigo
    all e: Estrada, s: e.inicio + e.inicio.*proxSegmento, ss: s.subSegmentos + s.subSegmentos.*proxSubSegmento |
        ss.elemento in obstaculo implies
            some prev: *(~proxSubSegmento)[ss] | prev.elemento in sinal
}

fact {
    regraPerigo[PerigoLomba + PerigoLombaOuDepressao, Lomba] and
    regraPerigo[PerigoDepressao + PerigoLombaOuDepressao, Depressao] and
    regraPerigo[PerigoPassadeira, Passadeira] and
    regraPerigo[PerigoTunel, Tunel]
}

// Regras Sinais de Cedência

pred regraCruzamentoEntroncamento[sinal: set Cedencia, intersecao: set Intercecao] {
    // Antes de uma interseção com uma via sem prioridade deve existir uma sinalização de cedência
    all e: Estrada, s: e.inicio + e.inicio.*proxSegmento |
        (some s.inter and s.inter in intersecao and 
            (s.inter in Rotunda or
             (s.inter in Cruzamento and s.inter.(Cruzamento <: comPrioridade) = True) or 
             (s.inter in Entroncamento and s.inter.(Entroncamento <: comPrioridade) = True)))
        implies
            some prev: (~proxSegmento[s]).subSegmentos | prev.elemento in sinal
}

fact {
    regraCruzamentoEntroncamento[CedenciaRotunda, Rotunda] and
    regraCruzamentoEntroncamento[CedenciaCruzamento, Cruzamento] and
    regraCruzamentoEntroncamento[CedenciaEntroncamento, Entroncamento]
}

fact regraEntroncamentoSemPrioridade {
    all e1, e2: Estrada, s1: e1.inicio + e1.inicio.*proxSegmento, s2: e2.inicio + e2.inicio.*proxSegmento |
        ((some s1.inter and s1.inter in Entroncamento and s1.inter.(Entroncamento <: comPrioridade) = True) and
        (some s2.inter and s2.inter in Entroncamento and s2.inter.(Entroncamento <: comPrioridade) = False) and
        (s1.inter.id = s2.inter.id))
        implies some prev: (~proxSegmento[s2]).subSegmentos | prev.elemento in CedenciaPassagem + CedenciaStop
}

fact regraCruzamentoSemPrioridade {
    all e1, e2: Estrada, s1: e1.inicio + e1.inicio.*proxSegmento, s2: e2.inicio + e2.inicio.*proxSegmento |
        (((some s1.inter and s1.inter in Cruzamento and s1.inter.(Cruzamento <: comPrioridade) = True)) and
        (some s2.inter and s2.inter in Cruzamento and s2.inter.(Cruzamento <: comPrioridade) = False) and
        (s1.inter.id = s2.inter.id))
        implies some prev: (~proxSegmento[s2]).subSegmentos | prev.elemento in CedenciaPassagem + CedenciaStop
}

fact EstradaStructure {
    all e: Estrada |
        some e.inicio // Every Estrada has an initial Segmento
}

pred example1 {
    one e: Estrada |
        e.id = "N205" and
        e.inicio.inter = Cruzamento and
        e.inicio.subSegmentos.elemento = PerigoLomba and
        e.inicio.subSegmentos.proxSubSegmento.elemento = Lomba and
        e.inicio.proxSegmento.inter = Rotunda
}

run example1 for 1 Universo, 5 Elemento, 1 Estrada, 3 Segmento, 3 SubSegmento, 2 Cruzamento, 2 Rotunda, 2 Lomba, 2 PerigoLomba, exactly 2 String

// pred sampleInstance {
//     // Create one Estrada with a series of connected segments and subsegments
//     one e: Estrada |
//         e.inicio.elemento = Lomba and
//         e.inicio.subSegmentos.elemento = PerigoLomba and
//         e.inicio.subSegmentos.proxSubSegmento.elemento = Depressao
// }
