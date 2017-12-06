package ServerController;

import java.awt.Color;
import java.util.ArrayList;
import java.util.Random;
import java.util.Stack;

import javax.swing.JOptionPane;

import CardModel.WildCard;
import GameModel.Game;
import GameModel.Player;
import Interfaces.GameConstants;
import View.Session;
import View.UNOCard;

public class Server implements GameConstants {

	/*@ public initially game != null;
	  @*/
	private /*@ spec_public nullable @*/ Game game;

	/*@ public initially session != null;
	  @*/
	private /*@ spec_public nullable @*/ Session session;

	/*@ public initially playedCards.size() == 1;
	  @ public constraint \old(playedCards) == playedCards;
	  @ public constraint \old(playedCards.size()) <= playedCards.size();
	  @*/
	private /*@ spec_public nullable @*/ Stack<UNOCard> playedCards = new Stack<>();

	/*@ public constraint (\old(canPlay) == false) ==> canPlay == false;
	  @*/
	public boolean canPlay = true;

	/*@ public initially mode == vsPC || mode == MANUAL;
	  @*/
	private /*@ spec_public @*/ int mode;

	public Server() {
		mode = requestMode();
		game = new Game(mode);

		// First Card
		UNOCard firstCard = game.getCard();
		modifyFirstCard(firstCard);

		playedCards.add(firstCard);
		session = new Session(game, firstCard);

		game.whoseTurn();
	}

	//return if it's 2-Player's mode or PC-mode
	/*@ assignable \nothing;
	  @ ensures \result == vsPC || \result == MANUAL;
	  @*/
	private int requestMode() {

		Object[] options = { "vs PC", "Manual", "Cancel" };

		int n = JOptionPane.showOptionDialog(null, "Choose a Game Mode to play", "Game Mode",
				JOptionPane.YES_NO_CANCEL_OPTION, JOptionPane.QUESTION_MESSAGE, null, options, options[0]);

		if (n == 2)
			System.exit(1);

		return GAMEMODES[n];
	}

	//custom settings for the first card
	/*@ 	requires firstCard.getType() == WILD;
	  @ 	assignable \nothing;
	  @ 	ensures ((WildCard) firstCard).getWildColor() != null;
	  @ 	ensures \old(firstCard) == firstCard;
	  @ also
	  @ 	requires firstCard.getType() != WILD;
	  @ 	assignable \nothing;
	  @ 	ensures \old(firstCard) == firstCard;
	  @*/
	private void modifyFirstCard(/*@ non_null @*/ UNOCard firstCard) {
		firstCard.removeMouseListener(CARDLISTENER);
		if (firstCard.getType() == WILD) {
			int random = new Random().nextInt() % 4;
			try {
				((WildCard) firstCard).useWildColor(UNO_COLORS[Math.abs(random)]);
			} catch (Exception ex) {
				System.out.println("something wrong with modifyFirstcard");
			}
		}
	}

	//return Main Panel
	/*@ requires session != null;
	  @ ensures \result == session;
	  @*/
	public /*@ pure @*/ Session getSession() {
		return this.session;
	}

	//request to play a card
	public void playThisCard(/*@ non_null @*/ UNOCard clickedCard) {

		// Check player's turn
		if (!isHisTurn(clickedCard)) {
			infoPanel.setError("It's not your turn");
			infoPanel.repaint();
		} else {

			// Card validation
			if (isValidMove(clickedCard)) {

				clickedCard.removeMouseListener(CARDLISTENER);
				playedCards.add(clickedCard);
				game.removePlayedCard(clickedCard);

				// function cards ??
				switch (clickedCard.getType()) {
				case ACTION:
					performAction(clickedCard);
					break;
				case WILD:
					performWild((WildCard) clickedCard);
					break;
				default:
					break;
				}

				game.switchTurn();
				session.updatePanel(clickedCard);
				checkResults();
			} else {
				infoPanel.setError("invalid move");
				infoPanel.repaint();
			}

		}

		if (mode == vsPC && canPlay) {
			if (game.isPCsTurn()) {
				game.playPC(peekTopCard());
			}
		}
	}

	//Check if the game is over
	private void checkResults() {

		if (game.isOver()) {
			canPlay = false;
			infoPanel.updateText("GAME OVER");
		}
	}

	//check player's turn
	public /*@ pure @*/ boolean isHisTurn(/*@ non_null @*/ UNOCard clickedCard) {

		for (Player p : game.getPlayers()) {
			if (p.hasCard(clickedCard) && p.isMyTurn())
				return true;
		}
		return false;
	}

	//check if it is a valid card
	/*@ requires peekTopCard() != null;
	  @ ensures \result == (playedCard.getColor().equals(peekTopCard().getColor())
	  @ 	|| playedCard.getValue().equals(peekTopCard().getValue())
	  @ 	|| playedCard.getType() == WILD
	  @ 	|| (peekTopCard().getType() == WILD
	  @ 		&& ((WildCard) peekTopCard()).getWildColor().equals(playedCard.getColor())));
	  @*/
	public /*@ pure @*/ boolean isValidMove(/*@ non_null @*/ UNOCard playedCard) {
		UNOCard topCard = peekTopCard();

		if (playedCard.getColor().equals(topCard.getColor()) || playedCard.getValue().equals(topCard.getValue())) {
			return true;
		}

		else if (playedCard.getType() == WILD) {
			return true;
		} else if (topCard.getType() == WILD) {
			Color color = ((WildCard) topCard).getWildColor();
			if (color.equals(playedCard.getColor()))
				return true;
		}
		return false;
	}

	// ActionCards
	/*@ 	requires game != null;
	  @ 	requires actionCard.getValue().equals(DRAW2PLUS)
	  @ 		|| actionCard.getValue().equals(REVERSE)
	  @ 		|| actionCard.getValue().equals(SKIP);
	  @ 	assignable game;
	  @ also
	  @ 	requires game != null;
	  @ 	assignable \nothing;
	  @*/
	private void performAction(/*@ non_null @*/ UNOCard actionCard) {

		// Draw2PLUS
		if (actionCard.getValue().equals(DRAW2PLUS))
			game.drawPlus(2);
		else if (actionCard.getValue().equals(REVERSE))
			game.switchTurn();
		else if (actionCard.getValue().equals(SKIP))
			game.switchTurn();
	}

	/*@ requires functionCard.getType() == WILD;
	  @	assignable game;
	  @*/
	private void performWild(/*@ non_null @*/ WildCard functionCard) {
		//System.out.println(game.whoseTurn());
		if (mode == vsPC && game.isPCsTurn()) {
			int random = new Random().nextInt() % 4;
			functionCard.useWildColor(UNO_COLORS[Math.abs(random)]);
		} else {

			ArrayList<String> colors = new ArrayList<>();
			colors.add("RED");
			colors.add("BLUE");
			colors.add("GREEN");
			colors.add("YELLOW");

			String chosenColor = (String) JOptionPane.showInputDialog(null, "Choose a color", "Wild Card Color",
					JOptionPane.DEFAULT_OPTION, null, colors.toArray(), null);

			functionCard.useWildColor(UNO_COLORS[colors.indexOf(chosenColor)]);
		}

		if (functionCard.getValue().equals(W_DRAW4PLUS))
			game.drawPlus(4);
	}

	/*@ requires game != null;
	  @ assignable game;
	  @*/
	public void requestCard() {
		game.drawCard(peekTopCard());

		if (mode == vsPC && !game.isOver()) {
			if (game.isPCsTurn())
				game.playPC(peekTopCard());
		}

		session.refreshPanel();
	}

	/*@ requires playedCards != null;
	  @ ensures \result == playedCards.peek();
	  @*/
	public /*@ pure @*/ UNOCard peekTopCard() {
		return playedCards.peek();
	}

	/*@ requires game != null;
	  @ assignable game;
	  @ ensures (\exists int i; 0 <= i && i < game.players.length;
	  @ 	game.players[i].getTotalCards() <= 2 ==> game.players[i].getSaidUNO());
	  @*/
	public void submitSaidUNO() {
		game.setSaidUNO();
	}
}
