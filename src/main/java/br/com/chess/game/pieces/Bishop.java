package br.com.chess.game.pieces;

import br.com.chess.game.boardgame.Board;
import br.com.chess.game.boardgame.Position;
import br.com.chess.game.chess.ChessPiece;
import br.com.chess.game.chess.utils.Color;

// CONCLUÍDO

public class Bishop extends ChessPiece {
    /*@ public normal_behavior
    @ requires board != null;
    @ requires color != null;
    @ ensures this.board == board;
    @ ensures this.color == color;
    @*/
    public Bishop(Board board, Color color) {
        super(board, color);
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

        boolean[][] mat = new boolean[getBoard().getRows()][getBoard().getColumns()];

        Position p = new Position(0, 0);

        // northwest
        p.setValues(position.getRow() - 1, position.getColumn() - 1);
        while (getBoard().positionExists(p) && !getBoard().thereIsAPiece(p)) {
            mat[p.getRow()][p.getColumn()] = true;
            p.setValues(p.getRow() - 1, p.getColumn() - 1);
        }
        if (getBoard().positionExists(p) && isThereOpponentPiece(p)) {
            mat[p.getRow()][p.getColumn()] = true;
        }

        // northeast
        p.setValues(position.getRow() - 1, position.getColumn() + 1);
        while (getBoard().positionExists(p) && !getBoard().thereIsAPiece(p)) {
            mat[p.getRow()][p.getColumn()] = true;
            p.setValues(p.getRow() - 1, p.getColumn() + 1);
        }
        if (getBoard().positionExists(p) && isThereOpponentPiece(p)) {
            mat[p.getRow()][p.getColumn()] = true;
        }

        // southeast
        p.setValues(position.getRow() + 1 , position.getColumn() + 1);
        while (getBoard().positionExists(p) && !getBoard().thereIsAPiece(p)) {
            mat[p.getRow()][p.getColumn()] = true;
            p.setValues(p.getRow() + 1, p.getColumn() + 1);
        }
        if (getBoard().positionExists(p) && isThereOpponentPiece(p)) {
            mat[p.getRow()][p.getColumn()] = true;
        }

        // below
        p.setValues(position.getRow() + 1, position.getColumn() - 1 );
        while (getBoard().positionExists(p) && !getBoard().thereIsAPiece(p)) {
            mat[p.getRow()][p.getColumn()] = true;
            p.setValues(p.getRow() + 1, p.getColumn() - 1);
        }
        if (getBoard().positionExists(p) && isThereOpponentPiece(p)) {
            mat[p.getRow()][p.getColumn()] = true;
        }

        return mat;
    }

    @Override
    public /*@ skipesc @*/ String toString(){
        return "B";
    }
}

