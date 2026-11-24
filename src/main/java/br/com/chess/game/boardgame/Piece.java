package br.com.chess.game.boardgame;

// CONCLUÍDO

public abstract class Piece {
    protected /*@ spec_public nullable @*/ Position position;
    private /*@ spec_public @*/ Board board;

    /*@ public normal_behavior
      @ ensures this.board == board;
      @ ensures this.position == null;
      @*/
    public /*@ pure @*/ Piece(Board board) {
        this.board = board;
        position = null;
    }

    /*@ protected normal_behavior
      @ ensures \result == board;
      @ assignable \nothing;
      @*/
    protected /*@ spec_pure @*/ Board getBoard() {
        return board;
    }

    /*@ public normal_behavior
      @ requires board != null;
      @ assignable \nothing;
      @ ensures \result != null;
      @ ensures \result.length == board.rows;
      @ ensures (\forall int i; 0 <= i && i < \result.length;
      @ \result[i] != null && \result[i].length == board.columns);
      @*/
    public abstract boolean[][] possibleMoves();

    /*@ public normal_behavior
      @ requires board != null;
      @ requires position != null;
      @ requires 0 <= position.getRow() && position.getRow() < board.rows;
      @ requires 0 <= position.getColumn() && position.getColumn() < board.columns;
      @ assignable \nothing;
      @*/
    public boolean possibleMove(Position position) {
        return possibleMoves()[position.getRow()][position.getColumn()];
    }
    
    /*@ public normal_behavior
      @ requires board != null;
      @ assignable \nothing;
      @*/
    public boolean isThereAnyPossibleMove() {
        boolean[][] mat = possibleMoves();
        /*@ loop_invariant 0 <= i && i <= mat.length;
          @ decreases mat.length - i;
          @*/
        for (int i = 0; i < mat.length; i++) {
            /*@ loop_invariant 0 <= j && j <= mat[i].length;
              @ decreases mat[i].length - j;
              @*/
            for (int j = 0; j < mat[i].length; j++) {
                if (mat[i][j]) {
                    return true;
                }
            }
        }
        return false;
    }
}