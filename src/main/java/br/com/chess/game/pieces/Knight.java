package br.com.chess.game.pieces;

import br.com.chess.game.boardgame.Board;
import br.com.chess.game.boardgame.Position;
import br.com.chess.game.chess.ChessPiece;
import br.com.chess.game.chess.utils.Color;

// CONCLUÍDO

public class Knight extends ChessPiece {
    /*@ public normal_behavior
    @ requires board != null;
    @ requires color != null;
    @ ensures this.board == board;
    @ ensures this.color == color;
     @*/
    public Knight(Board board, Color color) {
        super(board, color);
    }

    public /*@ skipesc @*/ String toString(){
        return "C";
    }
    
    /*@ private normal_behavior
    @ requires getBoard() != null;
    @ requires position != null;
    @ requires getBoard().positionExists(position);
    @ requires getBoard().piece(position) == null || getBoard().piece(position) instanceof ChessPiece;
    @ assignable \nothing;
    @ ensures \result <==> (getBoard().piece(position) == null || ((ChessPiece) getBoard().piece(position)).getColor() != getColor());
    @*/
    private boolean canMove(Position position){
        /*@ nullable @*/ ChessPiece p = (ChessPiece)getBoard().piece(position);
        return  p == null || p.getColor() != getColor();
    }

    /*@ also
    @ requires getBoard() != null;
    @ requires position != null;
    @ requires getBoard().positionExists(position);
    @ requires getBoard().getRows() > 0;
    @ requires getBoard().getColumns() > 0;
    @ assignable \nothing;
    @ ensures \result != null;
    @ ensures \fresh(\result);
    @ ensures \result.length == getBoard().getRows();
    @*/
    @Override
    public boolean[][] possibleMoves() {
        boolean[][] mat= new boolean[getBoard().getRows()][getBoard().getColumns()];
        Position p = new Position(0,0);

        p.setValues(position.getRow() - 1, position.getColumn() - 2);
        if (getBoard().positionExists(p) && canMove(p)) {
            mat[p.getRow()][p.getColumn()] = true;
        }

        p.setValues(position.getRow() - 2, position.getColumn() - 1);
        if (getBoard().positionExists(p) && canMove(p)) {
            mat[p.getRow()][p.getColumn()] = true;
        }

        p.setValues(position.getRow() - 2, position.getColumn() + 1);
        if (getBoard().positionExists(p) && canMove(p)) {
            mat[p.getRow()][p.getColumn()] = true;
        }

        p.setValues(position.getRow() - 1, position.getColumn() + 2);
        if (getBoard().positionExists(p) && canMove(p)) {
            mat[p.getRow()][p.getColumn()] = true;
        }

        p.setValues(position.getRow() + 1, position.getColumn() + 2);
        if (getBoard().positionExists(p) && canMove(p)) {
            mat[p.getRow()][p.getColumn()] = true;
        }

        p.setValues(position.getRow() + 2, position.getColumn() + 1);
        if (getBoard().positionExists(p) && canMove(p)) {
            mat[p.getRow()][p.getColumn()] = true;
        }

        p.setValues(position.getRow() + 2, position.getColumn() - 1);
        if (getBoard().positionExists(p) && canMove(p)) {
            mat[p.getRow()][p.getColumn()] = true;
        }

        p.setValues(position.getRow() + 1, position.getColumn() - 2);
        if (getBoard().positionExists(p) && canMove(p)) {
            mat[p.getRow()][p.getColumn()] = true;
        }


        return mat;
    }
}

