package br.com.chess.game.chess;

import br.com.chess.game.boardgame.Position;
import br.com.chess.game.chess.exceptions.ChessException;

public class ChessPosition {
    private /*@ spec_public @*/ char column;
    private /*@ spec_public non_null @*/ Integer row;

    /*@ public normal_behavior
    @ requires column >='a';
    @ requires column <= 'h';
    @ requires row >= 1;
    @ requires row <= 8;
    @ ensures this.column == column;
    @ ensures this.row == row;
    also
    @ public exceptional_behavior
    @ requires column < 'a' || column > 'h' || row < 1 || row > 8;
    @ signals_only ChessException;
    @*/
    public /*@ pure @*/ ChessPosition(char column, Integer row) {
        if(column < 'a' || column > 'h' || row < 1 || row > 8){
            throw new ChessException("Erro ao instanciar a posição no tabuleiro. Valores validos são de a1 até h8.");
        }
        this.column = column;
        this.row = row;
    }

    /*@ public normal_behavior
    @ ensures \result == column;
    @*/
    public /*@ pure @*/ char getColumn() {
        return column;
    }

    /*@ public normal_behavior
    @ ensures \result == row;
    @*/
    public /*@ pure @*/ Integer getRow() {
        return row;
    }

    //@ public invariant 'a' <= column && column <= 'h';
    //@ public invariant 1 <= row && row <= 8;

    /*@ protected normal_behavior
    @ ensures \fresh(\result);
    @ ensures \result.row == 8 - row;
    @ ensures \result.column == column - 'a';
    @*/
    protected /*@ pure @*/Position toPosition(){
        return new Position(8 - row, column - 'a'); 
    }

    /*@ protected normal_behavior
    @ requires 0 <= position.getRow();
    @ requires position.getRow() <= 7;
    @ requires 0 <= position.getColumn();
    @ requires position.getColumn() <= 7;
    @ ensures \fresh(\result);
    @ ensures \result.column == 'a' + position.getColumn();
    @ ensures \result.row == 8 - position.getRow();
    @*/
    protected /*@ pure @*/ static ChessPosition fromPosition(Position position){
        return new ChessPosition((char)('a' + position.getColumn()),8 - position.getRow());
    }

    @Override
    public /*@ skipesc @*/ String toString(){
        return "" + column + row;
    }

}
