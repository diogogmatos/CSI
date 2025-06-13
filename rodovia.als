sig Segmento {
    // Identificador único do segmento
    id: one Int,
    // Identificação da estrada a que o segmento pertence
    estrada: one String,
    // Delimita o começo do segmento
    elemento: one Elemento,
    // Regras presentes na sinalização do segmento atual
    // e/ou herdadas do segmento pai (se existir)
    regras: set Regulamentacao,
    // Subsegmentos que compõem o segmento atual
    segmentos: set Segmento,
}

sig Elemento {}

// Interseções

sig Intercecao extends Elemento {}

sig Rotunda extends Intercecao {}

sig Entroncamento extends Intercecao {}

sig Cruzamento extends Intercecao {}

// Obstáculos

sig Obstaculo extends Elemento {}

sig Passadeira extends Obstaculo {}

sig Lomba extends Obstaculo {}

sig Depressao extends Obstaculo {}

sig Tunel extends Obstaculo {}

// Sinais

sig Sinal extends Elemento {
    id: one String,
}

// Sinais de Perigo

sig Perigo extends Sinal {
    // Sinalizam um perigo que irá ocorrer no segmento
    sinaliza: one Obstaculo,
}

pred lomba {
    all s: Perigo | s.id = "A2a" implies s.sinaliza in Lomba
}

pred depressao {
    all s: Perigo | s.id = "A2b" implies s.sinaliza in Depressao
}

pred lombaOuDepressao {
    all s: Perigo | s.id = "A2c" implies s.sinaliza in Lomba or s.sinaliza in Depressao
}

pred p_passadeira {
    all s: Perigo | s.id = "A16a" implies s.sinaliza in Passadeira
}

pred tunel {
    all s: Perigo | s.id = "A20" implies s.sinaliza in Tunel
}

// Sinais de Regulamentação

sig Regulamentacao extends Sinal {}

// -- Sinais de Cedência de Passagem

sig CedenciaPassagem extends Regulamentacao {
    // Sinalizam uma regra de cedência a ser aplicada numa interseção
    sinaliza: one Intercecao,
}

pred stop {
    // "Paragem obrigatória emcruzamentos ou entroncamentos"
    all s: CedenciaPassagem | s.id = "B2" implies s.sinaliza in Cruzamento or s.sinaliza in Entroncamento
}

pred aproximacaoRotunda {
    // "Aproximação de rotunda"
    all s: CedenciaPassagem | s.id = "B7" implies s.sinaliza in Rotunda
}

pred cruzamento {
    // "Cruzamento com via sem prioridade"
    all s: CedenciaPassagem | s.id = "B8" implies s.sinaliza in Cruzamento
}

pred entroncamento {
    // "Entroncamento com via sem prioridade"
    all s: CedenciaPassagem | s.id = "B9a" or s.id = "B9b" or s.id = "B9c" or s.id = "B9d" implies s.sinaliza in Entroncamento
}

// -- Sinais de Proibição

sig Proibicao extends Regulamentacao {}

pred dependenciaDeSinaisProibicao {
    // Um sinal de proibição imposto a veículos em marcha deve ser sucedido por um sinal de fim dessa proibição

    // Velocidade máxima
    all s: Segmento | s.elemento in Proibicao and s.elemento.id = "C13"
    implies (some ss: s.segmentos | ss.elemento in Proibicao and (ss.elemento.id = "C20b" or ss.elemento.id = "C20a"))

    // Proibição de ultrapassagem
    all s: Segmento | s.elemento in Proibicao and s.elemento.id = "C14a"
    implies (some ss: s.segmentos | ss.elemento in Proibicao and (ss.elemento.id = "C20c" or ss.elemento.id = "C20a"))

    // Proibição de ultrapassagem para veículos pesados
    all s: Segmento | s.elemento in Proibicao and s.elemento.id = "C14b"
    implies (some ss: s.segmentos | ss.elemento in Proibicao and (ss.elemento.id = "C20d" or ss.elemento.id = "C20a"))

    // Proibição de ultrapassagem para motociclos e ciclomotores
    all s: Segmento | s.elemento in Proibicao and s.elemento.id = "C14c"
    implies (some ss: s.segmentos | ss.elemento in Proibicao and (ss.elemento.id = "C20e" or ss.elemento.id = "C20a"))
}

// -- Sinais de Obrigação

sig Obrigacao extends Regulamentacao {
    sinaliza: lone Elemento,
}

pred rotunda {
    all s: Obrigacao | s.id = "D4" implies (some ss: s.sinaliza | ss in Rotunda)
}

// -- Sinais de Informação

sig Informacao extends Sinal {
    sinaliza: one Elemento,
}

pred i_passadeira {
    all s: Informacao | s.id = "H7" implies s.sinaliza in Passadeira
}

// Regras de Trânsito

pred inv1 {
    // Antes de um obstaculo deve existir uma sinalização de perigo
    all o: Obstaculo | some p: Perigo | p.sinaliza = o
}

pred inv2 {
    // Antes de uma lomba deve existir uma sinalização de perigo
    all l: Lomba | some p: Perigo | p.sinaliza = l and (p.id = "A2a" or p.id = "A2c")
}

pred inv3 {
    // Antes de uma depressão deve existir uma sinalização de perigo
    all d: Depressao | some p: Perigo | p.sinaliza = d and (p.id = "A2b" or p.id = "A2c")
}

pred inv4 {
    // Antes de uma passadeira deve existir uma sinalização de perigo
    all pa: Passadeira | some p: Perigo | p.sinaliza = pa and p.id = "A16a"
}

pred inv5 {
    // Antes de uma interseção deve existir uma sinalização de cedência de passagem, de algum tipo
    all i: Intercecao | some s: CedenciaPassagem | s.sinaliza = i
}

pred inv6 {
    // Antes de uma rotunda deve existir uma sinalização de aproximação de rotunda e uma sinalização de cedência de passagem
    all r: Rotunda | some s1, s2: CedenciaPassagem | s1.id = "B7" and s2.id = "B1" and s1.sinaliza = r and s2.sinaliza = r
}