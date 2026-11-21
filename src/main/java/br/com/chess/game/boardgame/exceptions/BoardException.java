package br.com.chess.game.boardgame.exceptions;

// CONCLUÍDO

public class BoardException extends RuntimeException {
    private static final long serialVersionUID = 1L;

    /*@ public normal_behavior
    @ assignable \nothing;
    @*/
    public /*@ pure @*/BoardException(String msg){
        super(msg);
    }
}
