package br.com.chess.game.chess.exceptions;

import br.com.chess.game.boardgame.exceptions.BoardException;

// CONCLUÍDO

public class ChessException extends BoardException {
    private static final long serialVersionUID = 1L;

    /*@ public normal_behavior
    @ assignable \nothing;
    @*/
    public /*@ pure @*/ ChessException(String msg){
        super(msg);
    }

}