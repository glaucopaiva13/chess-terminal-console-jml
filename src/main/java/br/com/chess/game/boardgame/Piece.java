package br.com.chess.game.boardgame;

public abstract class Piece {
    protected /*@ spec_public nullable @*/ Position position;
    private /*@ spec_public @*/ Board board;

    /*@ public normal_behaviour
    @ ensures this.board == board;
    @ ensures this.position == null;
     */
    public Piece(Board board) {
        this.board = board;
        position = null;
    }

    /* @ protected normal_behaviour
    @ ensures \result == board;
     */
    protected /*@ pure @*/ Board getBoard() {
        return board;
    }

    public /*@ skipesc @*/ abstract boolean[][] possibleMoves();

    public /*@ skipesc @*/ boolean possibleMove(Position position) {
        return possibleMoves()[position.getRow()][position.getColumn()];
    }

    public /*@ skipesc @*/ boolean isThereAnyPossibleMove() {
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
