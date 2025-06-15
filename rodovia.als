// Utils

enum Bool { True, False }

// Main Code

sig Estrada {
    id: one String, -- identificador única da estrada
    inicio: one Segmento, -- cabeça da lista ligada de segmentos que compõe a estrada
}

sig Segmento {
    inter: lone Intercecao, -- delimita o começo do segmento
    // regras: set Regulamentacao, -- regras do segmento atual e as herdadas do segmento anterior (se existir) ??
    proxSegmento: lone Segmento, -- próximo segmento na lista
    subSegmentos: lone SubSegmento -- cabeça da lista ligada de subsegmentos
}

sig SubSegmento {
    elemento: one Sinal + Obstaculo, 
    proxSubSegmento: lone SubSegmento
}

pred regrasBase {
    // Todo o segmento deve ser alcançável a partir de uma estrada
    all s: Segmento | some e: Estrada | s in e.inicio.*proxSegmento
    // Todo o subsegmento deve ser alcançável a partir de uma estrada por via de um segmento
    all ss: SubSegmento | some s: Segmento | ss in s.subSegmentos.*proxSubSegmento
    // Um loop de segmentos não pode existir
    all s: Segmento | not (s in s.^proxSegmento)
    // Um loop de subsegmentos não pode existir
    all ss: SubSegmento | not (ss in ss.^proxSubSegmento)
    // Uma interseção deve estar associada a um segmento
    all i: Intercecao | some inter.i
    // Um sinal ou obstáculo deve estar associado a um subsegmento
    all so: (Sinal + Obstaculo) | some elemento.so
    // O id de uma estrada deve ser diferente do id de uma interseção
    all e: Estrada, i: Intercecao | e.id != i.id
    // Uma estrada deve ter um identificador único
    all e1, e2: Estrada | e1.id = e2.id implies e1 = e2
    // O início da estrada deve ser um segmento único
    all e1, e2: Estrada | e1.inicio = e2.inicio implies e1 = e2
    // Estradas diferentes não têm segmentos em comum
    all e1, e2: Estrada | e1 != e2 implies no e1.inicio.*proxSegmento & e2.inicio.*proxSegmento
    // Segmentos não partilham subsegmentos
    all s1, s2: Segmento | s1 != s2 implies no s1.subSegmentos.*proxSubSegmento & s2.subSegmentos.*proxSubSegmento
    // Estradas diferentes não têm subsegmentos em comum
    all e1, e2: Estrada | e1 != e2 implies no e1.inicio.subSegmentos.*proxSubSegmento & e2.inicio.subSegmentos.*proxSubSegmento
    // Uma estrada termina numa rotunda ou segmento sem saída
    all s: Segmento | s.inter in SemSaida + Rotunda implies (s.proxSegmento = none and s.subSegmentos = none)
    
    // Instancias de Intercecao nao sao partilhadas por segmentos
    all i : Intercecao, s1, s2: Segmento | s1.inter = i and s2.inter = i implies s1 = s2 
    // Instancias de Sinal ou Obstaculo nao sao partilhadas por subsegmentos
    all so: (Sinal + Obstaculo), ss1, ss2: SubSegmento | ss1.elemento = so and ss2.elemento = so implies ss1 = ss2

    // Num entroncamento com prioridades iguais, uma das estradas deve terminar
    // all e1, e2: Estrada, s1: e1.inicio.*proxSegmento, s2: e2.inicio.*proxSegmento |
    //     s1.inter in Entroncamento and s2.inter in Entroncamento and
    //     s1.inter.id = s2.inter.id and s1.inter.(Entroncamento <: comPrioridade) = s2.inter.(Entroncamento <: comPrioridade)
    //     implies (((s1.proxSegmento = none and s1.subSegmentos = none) or (s2.proxSegmento = none and s2.subSegmentos = none))
    //     and not (s1.proxSegmento = none and s1.subSegmentos = none and s2.proxSegmento = none and s2.subSegmentos = none))
    // Num entroncamento com prioridades opostas, a estrada sem prioridade deve terminar
    // all e1, e2: Estrada, s1: e1.inicio.*proxSegmento, s2: e2.inicio.*proxSegmento |
    //     s1.inter in Entroncamento and s2.inter in Entroncamento and
    //     s1.inter.id = s2.inter.id and s1.inter.(Entroncamento <: comPrioridade) = True and s2.inter.(Entroncamento <: comPrioridade) = False
    //     implies s2.proxSegmento = none and s2.subSegmentos = none
    // Entroncamentos devem ser partilhados por exatos 2 segmentos
    all e: Entroncamento |
        some e1, e2: Estrada, s1: e1.inicio.*proxSegmento, s2: e2.inicio.*proxSegmento |
        s1.inter in Entroncamento and s2.inter in Entroncamento and
        s1.inter.id = s2.inter.id and
        s1.inter.id = e.id and
        e1 != e2 
    // all s: Segmento | s.inter in Entroncamento implies (some os: Segmento | os != s and os.inter.id = s.inter.id)
    // all i: Entroncamento | one s1, s2: Segmento |
    //     s1 != s2 and s1.inter.id = i.id and s2.inter.id = i.id
    // Rotundas devem ser partilhadas por pelo menos dois segmentos
    all r: Rotunda |
        some s1, s2: Segmento |
        s1 != s2 and s1.inter.id = r.id and s2.inter.id = r.id
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
sig SemSaida extends Intercecao {}

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

// As estradas dos cruzamentos e entroncamentos não podem ambas ter prioridade
pred regraPrioridade {
    all s1, s2: Segmento |
    s1.inter in Cruzamento + Entroncamento and
    s2.inter in Cruzamento + Entroncamento and
    s1.inter.id = s2.inter.id and s1 != s2 implies
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

// -- Regras Sinais de Perigo

pred regraPerigo[sinal: set Perigo, obstaculo: set Obstaculo] {
    // Antes de um obstaculo deve existir uma sinalização de perigo
    all e: Estrada, s: e.inicio.*proxSegmento, ss: s.subSegmentos.*proxSubSegmento |
        ss.elemento in obstaculo implies
            some prev: *(~proxSubSegmento)[ss] | prev.elemento in sinal
}

pred regrasPerigo {
    regraPerigo[PerigoLomba + PerigoLombaOuDepressao, Lomba] and
    regraPerigo[PerigoDepressao + PerigoLombaOuDepressao, Depressao] and
    regraPerigo[PerigoPassadeira, Passadeira] and
    regraPerigo[PerigoTunel, Tunel]
}

// -- Regras Sinais de Cedência

pred regraCruzamentoEntroncamento[sinal: set Cedencia, intersecao: set Intercecao] {
    // Antes de uma interseção com uma via sem prioridade deve existir uma sinalização de cedência
    all e: Estrada, s: e.inicio.*proxSegmento |
        (~proxSegmento[s] != none and some s.inter and s.inter in intersecao and 
            (s.inter in Rotunda or
             (s.inter in Cruzamento and s.inter.(Cruzamento <: comPrioridade) = True) or 
             (s.inter in Entroncamento and s.inter.(Entroncamento <: comPrioridade) = True)))
        implies
            one prev: (~proxSegmento[s]).subSegmentos | prev.elemento in sinal
}

pred regraEntroncamentoSemPrioridade {
    all e1, e2: Estrada, s1: e1.inicio.*proxSegmento, s2: e2.inicio.*proxSegmento |
        (~proxSegmento[s2] != none and 
        (some s1.inter and s1.inter in Entroncamento and s1.inter.(Entroncamento <: comPrioridade) = True) and
        (some s2.inter and s2.inter in Entroncamento and s2.inter.(Entroncamento <: comPrioridade) = False) and
        (s1.inter.id = s2.inter.id))
        implies one prev: (~proxSegmento[s2]).subSegmentos | prev.elemento in CedenciaPassagem + CedenciaStop
}

pred regraCruzamentoSemPrioridade {
    all e1, e2: Estrada, s1: e1.inicio.*proxSegmento, s2: e2.inicio.*proxSegmento |
        (~proxSegmento[s2] != none and (
        (some s1.inter and s1.inter in Cruzamento and s1.inter.(Cruzamento <: comPrioridade) = True)) and
        (some s2.inter and s2.inter in Cruzamento and s2.inter.(Cruzamento <: comPrioridade) = False) and
        (s1.inter.id = s2.inter.id))
        implies some prev: (~proxSegmento[s2]).subSegmentos | prev.elemento in CedenciaPassagem + CedenciaStop
}

pred regrasCedencia {
    regraCruzamentoEntroncamento[CedenciaRotunda, Rotunda] and
    regraCruzamentoEntroncamento[CedenciaCruzamento, Cruzamento] and
    regraCruzamentoEntroncamento[CedenciaEntroncamento, Entroncamento] and
    regraEntroncamentoSemPrioridade and
    regraCruzamentoSemPrioridade
}

// Encontrar modelos válidos
run {
    some s: String | s = "s1" or s = "s2" or s = "s3" or s = "s4" or s = "s5" or s = "s6" or s = "s7"
    some Estrada
    // some Segmento
    // some proxSegmento
    // some proxSubSegmento
    // some SubSegmento
    // some PerigoLomba
    // some Lomba
    // some CedenciaStop
    some Entroncamento
    regrasBase
    regraPrioridade
    regrasPerigo
    regrasCedencia
} for 5 Estrada, 5 Segmento, 5 SubSegmento, 5 Elemento

// Encontrar modelos inválidos
check {
    not (all s: Segmento | not (s in s.^proxSegmento))
}
