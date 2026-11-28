package br.com.chess.game.views;

import br.com.chess.game.chess.ChessMatch;
import br.com.chess.game.chess.ChessPiece;
import br.com.chess.game.chess.ChessPosition;
import br.com.chess.game.chess.utils.Color;
import br.com.chess.game.views.utils.BoardColors;

import java.util.*;
import java.util.stream.Collectors;

public class BoardView {

    /*@ public normal_behavior
      @ assignable System.out.*;
      @*/
    public static void clearScreen() {
        System.out.print("\033[H\033[2J");
        System.out.flush();
    }

    /*@ public behavior
      @ requires sc != null;
      @ assignable \everything;
      @ ensures \result != null;
      @ signals (InputMismatchException e) true;
      @*/
    public static ChessPosition readChessPosition(Scanner sc) {
        try {
            String s = sc.nextLine();
            char column = s.charAt(0);
            int row = Integer.parseInt(s.substring(1));
            return new ChessPosition(column, row);
        } catch (RuntimeException e) {
            throw new InputMismatchException("Erro ao ler a posição no tabuleiro. Valores validos entre a1 até h8");
        }
    }

    /*@ public behavior
      @ requires chessMatch != null;
      @ requires chessMatch.getPieces() != null && chessMatch.getPieces().length == 8;
      @ requires (\forall int i; 0 <= i && i < 8; chessMatch.getPieces()[i] != null && chessMatch.getPieces()[i].length == 8);
      @ requires capturedPieces != null;
      @ requires (\forall int i; 0 <= i && i < capturedPieces.size(); capturedPieces.get(i) != null);
      @ assignable \everything;
      @*/
    public static void printMatch(ChessMatch chessMatch, List<ChessPiece> capturedPieces) {
        printBoard(chessMatch.getPieces());
        System.out.println();
        capturedPieces(capturedPieces);
        System.out.println("Turno: " + chessMatch.getTurn());
        if (!chessMatch.isCheckMate()) {
            System.out.println("Esperando o joagador: " + chessMatch.getCurrentPlayer());
            if (chessMatch.isCheck()) {
                System.out.println("Check!");
            }
        } else {
            System.out.println("CHECKMATE!");
            System.out.println("Vencedor: " + chessMatch.getCurrentPlayer());
        }
    }

    /*@ public normal_behavior
      @ requires pieces != null && pieces.length == 8;
      @ requires (\forall int i; 0 <= i && i < pieces.length; pieces[i] != null && pieces[i].length == 8);
      @ assignable \everything;
      @*/
    public static void printBoard(/*@ nullable @*/ ChessPiece[][] pieces) {
        /*@ loop_invariant 0 <= i && i <= 8;
          @ loop_invariant pieces != null && pieces.length == 8;
          @ loop_invariant (\forall int k; 0 <= k && k < 8; pieces[k] != null && pieces[k].length == 8);
          @ loop_assigns \everything;
          @ decreases 8 - i;
          @*/
        for (int i = 0; i < pieces.length; i++) {
            System.out.print(8 - i);
            System.out.print(" ");
            /*@ loop_invariant 0 <= j && j <= 8;
              @ loop_invariant 0 <= i && i < 8;
              @ loop_invariant pieces != null && pieces.length == 8;
              @ loop_invariant (\forall int k; 0 <= k && k < 8; pieces[k] != null && pieces[k].length == 8);
              @ loop_assigns \everything;
              @ decreases 8 - j;
              @*/
            for (int j = 0; j < pieces.length; j++) {
                printPiece(pieces[i][j], false);
            }
            System.out.println();
        }
        System.out.println("  a b c d e f g h");
    }

    /*@ public normal_behavior
      @ requires pieces != null && pieces.length == 8;
      @ requires (\forall int i; 0 <= i && i < pieces.length; pieces[i] != null && pieces[i].length == 8);
      @ requires possibleMoves != null && possibleMoves.length == 8;
      @ requires (\forall int i; 0 <= i && i < possibleMoves.length; possibleMoves[i] != null && possibleMoves[i].length == 8);
      @ assignable \everything;
      @*/
    public static void printBoard(/*@ nullable @*/ ChessPiece[][] pieces, boolean[][] possibleMoves) {
        /*@ loop_invariant 0 <= i && i <= 8;
          @ loop_invariant pieces != null && pieces.length == 8;
          @ loop_invariant (\forall int k; 0 <= k && k < 8; pieces[k] != null && pieces[k].length == 8);
          @ loop_invariant possibleMoves != null && possibleMoves.length == 8;
          @ loop_invariant (\forall int k; 0 <= k && k < 8; possibleMoves[k] != null && possibleMoves[k].length == 8);
          @ loop_assigns \everything;
          @ decreases 8 - i;
          @*/
        for (int i = 0; i < pieces.length; i++) {
            System.out.print(8 - i);
            System.out.print(" ");
            /*@ loop_invariant 0 <= j && j <= 8;
              @ loop_invariant 0 <= i && i < 8;
              @ loop_invariant pieces != null && pieces.length == 8;
              @ loop_invariant (\forall int k; 0 <= k && k < 8; pieces[k] != null && pieces[k].length == 8);
              @ loop_invariant possibleMoves != null && possibleMoves.length == 8;
              @ loop_invariant (\forall int k; 0 <= k && k < 8; possibleMoves[k] != null && possibleMoves[k].length == 8);
              @ loop_assigns \everything;
              @ decreases 8 - j;
              @*/
            for (int j = 0; j < pieces.length; j++) {
                printPiece(pieces[i][j], possibleMoves[i][j]);
            }
            System.out.println();
        }
        System.out.println("  a b c d e f g h");
    }

    /*@ private normal_behavior
      @ assignable System.out.*;
      @*/
    private /*@ skipesc @*/ static void printPiece(/*@ nullable @*/ ChessPiece piece, boolean background) {
        if (background) {
            System.out.print(BoardColors.ANSI_BLUE_BACKGROUND);
        }
        if (piece == null) {
            System.out.print("-" + BoardColors.ANSI_RESET);
        } else {
            if (piece.getColor() == Color.WHITE) {
                System.out.print(BoardColors.ANSI_WHITE + piece + BoardColors.ANSI_RESET);
            } else {
                System.out.print(BoardColors.ANSI_YELLOW + piece + BoardColors.ANSI_RESET);
            }
        }
        System.out.print(" ");
    }

    /*@ private normal_behavior
      @ requires chessPieces != null;
      @ assignable System.out.*;
      @*/
    private /*@ skipesc @*/ static void capturedPieces(List<ChessPiece> chessPieces) {
        List<ChessPiece> white = chessPieces.stream()
                .filter(x -> x != null && x.getColor() == Color.WHITE)
                .collect(Collectors.toList());

        List<ChessPiece> black = chessPieces.stream()
                .filter(x -> x != null && x.getColor() == Color.BLACK)
                .collect(Collectors.toList());
        System.out.println("Peças capturadas: ");
        System.out.print("Peças brancas: ");
        System.out.print(BoardColors.ANSI_WHITE);
        System.out.println(Arrays.toString(white.toArray()));
        System.out.print(BoardColors.ANSI_RESET);
        System.out.print("Peças pretas: ");
        System.out.print(BoardColors.ANSI_YELLOW);
        System.out.println(Arrays.toString(black.toArray()));
    }
}