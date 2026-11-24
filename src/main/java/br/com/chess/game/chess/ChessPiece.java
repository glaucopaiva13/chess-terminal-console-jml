package br.com.chess.game.chess;

import br.com.chess.game.boardgame.Board;
import br.com.chess.game.boardgame.Piece;
import br.com.chess.game.boardgame.Position;
import br.com.chess.game.chess.utils.Color;


public abstract class ChessPiece extends Piece {
    private /*@ spec_public @*/ Color color;
    private /*@ spec_public @*/ int moveCount;

    /*@ public normal_behavior
    @ requires board != null;
    @ requires color != null;
    @ ensures this.color == color;
    @ ensures this.board == board;
     */
    public /*@ pure @*/ChessPiece(Board board, Color color) {
        super(board);
        this.color = color;
    }

    /*@ public normal_behavior
    @ ensures \result == color;
    @ assignable \nothing;
    @*/
    public /*@ pure @*/ Color getColor() {
        return color;
    }

    /*@ public normal_behavior
    @ ensures \result == moveCount;
    @ assignable \nothing;
    @*/
    public /*@ pure @*/ int getMoveCount() {
        return moveCount;
    }

    /*@ public normal_behavior
    @ requires moveCount < Integer.MAX_VALUE;
    @ assignable moveCount;
    @ ensures moveCount == \old(moveCount) + 1;
    @*/
    public void increaseMoveCount(){
        moveCount++;
    }

    /*@ public normal_behavior
    @ requires moveCount > 0;
    @ assignable moveCount;
    @ ensures moveCount == \old(moveCount) - 1; 
    @*/
    public void decreaseMoveCount(){
        moveCount--;
    }

    /*@ protected normal_behavior
    @ requires position != null;
    @ requires getBoard() != null && getBoard().positionExists(position);
    @ requires getBoard().piece(position) == null || getBoard().piece(position) instanceof ChessPiece;
    @ assignable \nothing;
    @ ensures \result <==> (getBoard().piece(position) != null && ((ChessPiece) getBoard().piece(position)).getColor() != color);
    @*/
    protected /*@ pure @*/ boolean isThereOpponentPiece(Position position) {
        /*@ nullable @*/ ChessPiece p = (ChessPiece)getBoard().piece(position);
        return p != null && p.getColor() != color;
    }

    /*@ public normal_behavior
    @ requires position != null;
    @ requires 0 <= position.getRow() && position.getRow() < 8;
    @ requires 0 <= position.getColumn() && position.getColumn() < 8;
    @ assignable \nothing;
    @ ensures \result != null;
    @ ensures \result.getColumn() == (char) ('a' + position.getColumn());
    @ ensures \result.getRow() == 8 - position.getRow();
    @*/
    public /*@ pure @*/ ChessPosition getChessPosition(){
        return ChessPosition.fromPosition(position);
    }
}

