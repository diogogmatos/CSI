

sig Segmento {
    // Identificador único do segmento
    id: one Int,
    // Identificação da estrada a que o segmento pertence
    estrada: one String,
    // Delimita o começo do segmento
    elemento: one Elemento,
    // Regras presentes na sinalização do segmento atual
    // e/ou herdadas do segmento pai (se existir)
    regras: set Regra,
    // Subsegmentos que compõem o segmento atual
    segmentos: set Segmento,
}

sig Regra {
    nome: one String,
    descricao: one String,
}

// -- ELEMENTOS --

sig Elemento {

}

// Interseções

sig Intercecao in Elemento {

}

sig Rotunda in Intercecao {

}

sig Entroncamento in Intercecao {

}

sig Cruzamento in Intercecao {

}

// Sinais

sig Sinal in Elemento {

}

// Sinais de Perigo

sig Perigo in Sinal {
    // Sinalizam um perigo que irá ocorrer no segmento
    sinaliza: one Elemento,
}

// Sinais de Regulamentação

sig Regulamentacao in Sinal {
    // Estabelecem uma regra que deve ser cumprida em todo o segmento
    regra: one Regra,
}

sig Proibicao in Regulamentacao {
    // Podem ou não estar associados a outros sinais (ex: Proibido ultrapassar e Fim de proibição)
    depende: lone Sinal,
}

sig Obrigacao in Regulamentacao {

}

// Obstáculos

sig Obstaculo in Elemento {

}

sig Passadeira in Obstaculo {

}

sig Lomba in Obstaculo {

}

sig Depressao in Obstaculo {

}