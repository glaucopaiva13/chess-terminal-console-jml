package br.com.chess.game.boardgame;

import br.com.chess.game.boardgame.exceptions.BoardException;

public class Board {
    private /*@ spec_public non_null @*/ Integer rows;
    private /*@ spec_public non_null @*/ Integer columns;
    private /*@ spec_public nullable @*/ Piece [][] pieces;

    //@ public invariant rows >= 1;
    //@ public invariant columns >= 1;
    //@ public invariant pieces != null;
    //@ public invariant pieces.length == rows;
    //@ public invariant (\forall int i; 0 <= i && i < rows; pieces[i] != null && pieces[i].length == columns);

    /*@ public normal_behavior
      @ requires rows >= 1; 
      @ requires columns >= 1;
      @ ensures this.rows == rows;
      @ ensures this.columns == columns;
      @ ensures pieces != null;
      @ ensures pieces.length == rows;
      @ ensures (\forall int i; 0 <= i && i < rows; pieces[i] != null && pieces[i].length == columns);
      @ ensures (\forall int i, j; 0 <= i && i < rows && 0 <= j && j < columns; pieces[i][j] == null);
      @ also
      @ public exceptional_behavior
      @ requires rows < 1 || columns < 1;
      @ signals_only BoardException;
      @*/
    public Board(int rows, int columns) {
        if (rows < 1 || columns < 1) {
            throw new BoardException("Erro ao criar o tabuleiro: " +
                    "É necessario que haja pelo menos 1 linha e 1 coluna");
        }
        this.rows = rows;
        this.columns = columns;
        pieces = new Piece[rows][columns];
    }

    /*@ public normal_behavior
      @ ensures \result == rows;
      @*/
    public /*@ pure @*/ Integer getRows() {
        return rows;
    }

    /*@ public normal_behavior
      @ ensures \result == columns;
      @*/
    public /*@ pure @*/ Integer getColumns() {
        return columns;
    }

    /*@ public normal_behavior
      @ requires positionExists(row, column);
      @ ensures \result == pieces[row][column];
      @ also
      @ public exceptional_behavior
      @ requires !positionExists(row, column);
      @ signals_only BoardException;
      @*/
    public /*@ pure nullable @*/ Piece piece(Integer row, Integer column) {
        if (!positionExists(row, column)) {
            throw new BoardException("A posição fora do tabuleiro");
        }
        return pieces[row][column];
    }

    /*@ public normal_behavior
      @ requires positionExists(position);
      @ ensures \result == pieces[position.getRow()][position.getColumn()];
      @ also
      @ public exceptional_behavior
      @ requires !positionExists(position);
      @ signals_only BoardException;
      @*/
    public /*@ pure nullable @*/ Piece piece(Position position) {
        if (!positionExists(position)) {
            throw new BoardException("A posição fora do tabuleiro");
        }
        return pieces[position.getRow()][position.getColumn()];
    }

    /*@ public normal_behavior
      @ requires positionExists(position);
      @ requires pieces[position.getRow()][position.getColumn()] == null;
      @ assignable pieces[position.getRow()][position.getColumn()], piece.position;
      @ ensures pieces[position.getRow()][position.getColumn()] == piece;
      @ ensures piece.position == position;
      @ also
      @ public exceptional_behavior
      @ requires !positionExists(position) || pieces[position.getRow()][position.getColumn()] != null;
      @ assignable \nothing;
      @ signals_only BoardException;
      @*/
    public void placePiece(Piece piece, Position position) {
        // por algum motivo, dá muito problema com o operador "+" do Java e do override metodo toString, tive que mudar
        if (thereIsAPiece(position)) {
            throw new BoardException("Já existe uma peça na posição.");
        }
        pieces[position.getRow()][position.getColumn()] = piece;
        piece.position = position;
    }

    /*@ public normal_behavior
      @ requires positionExists(position);
      @ requires pieces[position.getRow()][position.getColumn()] == null;
      @ assignable \nothing;
      @ ensures \result == null;
      @ also
      @ public normal_behavior
      @ requires positionExists(position);
      @ requires pieces[position.getRow()][position.getColumn()] != null;
      @ assignable pieces[position.getRow()][position.getColumn()], pieces[position.getRow()][position.getColumn()].position;
      @ ensures \result == \old(pieces[position.getRow()][position.getColumn()]);
      @ ensures \result.position == null;
      @ ensures pieces[position.getRow()][position.getColumn()] == null;
      @ also
      @ public exceptional_behavior
      @ requires !positionExists(position);
      @ assignable \nothing;
      @ signals_only BoardException;
      @*/
    public /*@ nullable @*/ Piece removePiece(Position position) {
        if (!positionExists(position)) {
            throw new BoardException("A posição fora do tabuleiro");
        }
        if (piece(position) == null) {
            return null;
        }
        /*
        eu fiquei um tempo procurando errado para descobrir que era nesse metodo
        porque ele fazia uma escrita indevida na heap  */
        int row = position.getRow();
        int column = position.getColumn();
        Piece aux = piece(position);
        aux.position = null;
        pieces[row][column] = null;
        return aux;
    }

    /*@ public normal_behavior
      @ ensures \result == (0 <= row && row < rows && 0 <= column && column < columns);
      @*/
    private /*@ spec_public pure @*/ boolean positionExists(int row, int column) {
        return row >= 0 && row < rows && column >= 0 && column < columns;
    }

    /*@ public normal_behavior
      @ ensures \result == positionExists(position.getRow(), position.getColumn());
      @*/
    public /*@ pure @*/ boolean positionExists(Position position) {
        return positionExists(position.getRow(), position.getColumn());
    }

    /*@ public normal_behavior
      @ requires positionExists(position);
      @ ensures \result == (pieces[position.getRow()][position.getColumn()] != null);
      @ also
      @ public exceptional_behavior
      @ requires !positionExists(position);
      @ signals_only BoardException;
      @*/
    public /*@ pure @*/ boolean thereIsAPiece(Position position) {
        if (!positionExists(position)) {
            throw new BoardException("A posição fora do tabuleiro");
        }
        return piece(position) != null;
    }
}