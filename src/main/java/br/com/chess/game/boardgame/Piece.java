package br.com.chess.game.boardgame;

public abstract class Piece {
    protected /*@ spec_public nullable @*/ Position position;
    private /*@ spec_public @*/ Board board;

    /*@ public normal_behavior
    @ ensures this.board == board;
    @ ensures this.position == null;
     */
    public Piece(Board board) {
        this.board = board;
        position = null;
    }

    /* @ protected normal_behavior
    @ ensures \result == board;
     */
    protected /*@ pure @*/ Board getBoard() {
        return board;
    }

    public abstract boolean[][] possibleMoves();

    public boolean possibleMove(Position position) {
        return possibleMoves()[position.getRow()][position.getColumn()];
    }

    public boolean isThereAnyPossibleMove() {
        boolean[][] mat = possibleMoves();
        for (int i=0; i<mat.length; i++) {
            for (int j=0; j<mat.length; j++) {
                if (mat[i][j]) {
                    return true;
                }
            }
        }
        return false;
    }
}
