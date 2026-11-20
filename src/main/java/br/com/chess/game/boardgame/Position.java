package br.com.chess.game.boardgame;

public class Position {
    private /*@ spec_public @*/ int row;
    private /*@ spec_public @*/ int column;

    /*@ public normal_behavior
      @ ensures this.row == row;
      @ ensures this.column == column;
      @*/
    public Position(int row, int column) {
        this.row = row;
        this.column = column;
    }

    /*@ public normal_behavior
      @ ensures \result == row;
      @*/
    public /*@ pure @*/ int getRow() {
        return row;
    }

    public void setRow(int row) {
        this.row = row;
    }

    /*@ public normal_behavior
    @ ensures \result == column;
    @*/
    public /*@ pure @*/int getColumn() {
        return column;
    }

    public void setColumn(int column) {
        this.column = column;
    }

    public void setValues(int row, int column) {
        this.row = row;
        this.column = column;
    }

    @Override
    public /*@ skipesc @*/String toString() {
        return row + ", " + column;
    }
}
