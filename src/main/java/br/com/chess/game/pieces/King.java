package br.com.chess.game.pieces;

import br.com.chess.game.boardgame.Board;
import br.com.chess.game.boardgame.Position;
import br.com.chess.game.chess.ChessMatch;
import br.com.chess.game.chess.ChessPiece;
import br.com.chess.game.chess.utils.Color;

public class King extends ChessPiece {

    private /*@ spec_public @*/ ChessMatch chessMatch;

    /*@ public normal_behavior
    @ requires board != null;
    @ requires color != null;
    @ requires chessMatch != null;
    @ ensures this.board == board;
    @ ensures this.color == color;
    @ ensures this.chessMatch == chessMatch;
    @*/
    public /*@ pure @*/ King(Board board, Color color, ChessMatch chessMatch) {
        super(board, color);
        this.chessMatch = chessMatch;
    }

    /*@ public normal_behavior
    @ ensures \result == chessMatch;
     */
    public /*@ spec_pure @*/ ChessMatch getChessMatch() {
        return chessMatch;
    }

    @Override
    public /*@ skipesc @*/ String toString(){
        return "R";
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
        ChessPiece p = (ChessPiece)getBoard().piece(position);
        return  p == null || p.getColor() != getColor();
    }

    /*@ private normal_behavior
    @ requires getBoard() != null;
    @ requires position != null;
    @ requires getBoard().positionExists(position);
    @ requires getBoard().piece(position) == null || getBoard().piece(position) instanceof ChessPiece;
    @ assignable \nothing;
    @ ensures \result <==> (getBoard().piece(position) instanceof Rook && ((ChessPiece) getBoard().piece(position)).getColor() == getColor() && ((ChessPiece) getBoard().piece(position)).getMoveCount() == 0);
    @*/
    private boolean testRookCastling(Position position){
        ChessPiece p = (ChessPiece)getBoard().piece(position);
        return position !=null && p instanceof Rook && getColor() == getColor() && p.getMoveCount() == 0;
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

        //above
        p.setValues(position.getRow() - 1, position.getColumn());
        if(getBoard().positionExists(p) && canMove(p)){
            mat[p.getRow()][p.getColumn()] = true;
        }
        //below
        p.setValues(position.getRow() + 1, position.getColumn());
        if(getBoard().positionExists(p) && canMove(p)){
            mat[p.getRow()][p.getColumn()] = true;
        }
        //left
        p.setValues(position.getRow(), position.getColumn() - 1);
        if(getBoard().positionExists(p) && canMove(p)){
            mat[p.getRow()][p.getColumn()] = true;
        }

        //right
        p.setValues(position.getRow(), position.getColumn() + 1);
        if(getBoard().positionExists(p) && canMove(p)){
            mat[p.getRow()][p.getColumn()] = true;
        }


        p.setValues(position.getRow() - 1, position.getColumn() - 1);
        if(getBoard().positionExists(p) && canMove(p)){
            mat[p.getRow()][p.getColumn()] = true;
        }


        p.setValues(position.getRow() + 1, position.getColumn() + 1);
        if(getBoard().positionExists(p) && canMove(p)){
            mat[p.getRow()][p.getColumn()] = true;
        }


        p.setValues(position.getRow() + 1, position.getColumn() - 1);
        if(getBoard().positionExists(p) && canMove(p)){
            mat[p.getRow()][p.getColumn()] = true;
        }


        //southeast
        p.setValues(position.getRow() - 1, position.getColumn() + 1);
        if(getBoard().positionExists(p) && canMove(p)){
            mat[p.getRow()][p.getColumn()] = true;
        }


        //Special move castling
        if(getMoveCount() == 0 && !chessMatch.isCheck()){
            //# special move castling kingside rook
            Position positionT1 = new Position(position.getRow(), position.getColumn() + 3);
            if(testRookCastling(positionT1)){
                Position p1 = new Position(position.getRow(), position.getColumn() + 1);
                Position p2 = new Position(position.getRow(), position.getColumn() + 2);
                if(getBoard().piece(p1) == null && getBoard().piece(p2) == null){
                    mat[position.getRow()][position.getColumn() + 2] = true;
                }
            }
            //# special move castling queenside rook
            Position positionT2 = new Position(position.getRow(), position.getColumn() - 4);
            if(testRookCastling(positionT2)){
                Position p1 = new Position(position.getRow(), position.getColumn() - 1);
                Position p2 = new Position(position.getRow(), position.getColumn() - 2);
                Position p3 = new Position(position.getRow(), position.getColumn() - 3);
                if(getBoard().piece(p1) == null && getBoard().piece(p2) == null && getBoard().piece(p3) == null){
                    mat[position.getRow()][position.getColumn() - 2] = true;
                }
            }

        }
        return mat;
    }


}