package GameModel;

import java.util.Stack;

import javax.swing.JOptionPane;

import CardModel.WildCard;
import Interfaces.GameConstants;
import View.UNOCard;

public class Game implements GameConstants {

	/*@ public initially players != null;
	  @ public initially players.length == 2;
	  @ public invariant players.length == 2;
	  @ public invariant (\exists int i; 0 <= i && i < players.length;
	  @ 	players[i].getTotalCards() > 0);
	  @ public invariant (\exists int i; 0 <= i && i < players.length;
	  @ 	players[i].isMyTurn() <==> (\forall int j; 0 <= j && j < players.length;
	  @ 		j != i ==> !players[j].isMyTurn()));
	  @ public constraint (\forall int i; 0 <= i && i < players.length;
	  @ 	\old(players[i]) == players[i]);
	  @*/
	private /*@ spec_public nullable @*/ Player[] players;

	/*@ public initially isOver == false;
	  @ public invariant isOver == true ==> (\exists int i; 0 <= i && i < players.length;
	  @ 	players[i].getTotalCards() == 0 && (\forall int j; 0 <= j && j < players.length;
	  @ 		j != i ==> players[j].getTotalCards() > 0));
	  @*/
	private /*@ spec_public @*/ boolean isOver;

	/*@ public initially GAMEMODE == vsPC || GAMEMODE == MANUAL;
	  @ public invariant GAMEMODE == vsPC || GAMEMODE == MANUAL;
	  @ public constraint \old(GAMEMODE) == GAMEMODE;
	  @*/
	private /*@ spec_public @*/ int GAMEMODE;

	/*@ public initially (GAMEMODE == vsPC && pc != null) || (GAMEMODE == MANUAL && pc == null);
	  @ public constraint \old(pc) == pc;
	  @*/
	private /*@ spec_public nullable @*/ PC pc;

	/*@ public initially dealer != null;
	  @ public invariant dealer != null;
	  @ public constraint \old(dealer) == dealer;
	  @*/
	private /*@ spec_public nullable @*/ Dealer dealer;

	/*@ public initially cardStack != null;
	  @ public invariant cardStack != null;
	  @ public invariant (\forall int i; 0 <= i && i < cardStack.size();
	  @ 	cardStack.get(i) != null);
	  @ public constraint \old(cardStack) == cardStack;
	  @*/
	private /*@ spec_public nullable @*/ Stack<UNOCard> cardStack;


	public Game(int mode) {
		GAMEMODE = mode;

		//Create players
		String name = (GAMEMODE == MANUAL) ? JOptionPane.showInputDialog("Player 1") : "PC";
		String name2 = JOptionPane.showInputDialog("Player 2");

		if (GAMEMODE == vsPC)
			pc = new PC();

		Player player1 = (GAMEMODE == vsPC) ? pc : new Player(name);
		Player player2 = new Player(name2);
		player2.toggleTurn();				//Initially, player2's turn

		players = new Player[]{player1, player2};

		//Create Dealer
		dealer = new Dealer();
		cardStack = dealer.shuffle();
		dealer.spreadOut(players);

		isOver = false;
	}

	/*@ requires players != null;
	  @ ensures \result == players;
	  @*/
	public /*@ pure @*/ Player[] getPlayers() {
		return players;
	}

	/*@ requires dealer != null;
	  @ ensures \result != null;
	  @*/
	public /*@ pure @*/ UNOCard getCard() {
		return dealer.getCard();
	}

	/*@ requires playedCard != null;
	  @ requires players != null;
	  @ ensures (\forall int i; 0 < i && i < players.length;
	  @ 	\old(players[i]).hasCard(playedCard) ==> !players[i].hasCard(playedCard));
	  @*/
	public void removePlayedCard(/*@ non_null @*/ UNOCard playedCard) {

		for (Player p : players) {
			if (p.hasCard(playedCard)){
				p.removeCard(playedCard);

				if (p.getTotalCards() == 1 && !p.getSaidUNO()) {
					infoPanel.setError(p.getName() + " Forgot to say UNO");
					p.obtainCard(getCard());
					p.obtainCard(getCard());
				} else if(p.getTotalCards() > 2) {
					p.setSaidUNOFalse();
				}
			}
		}
	}

	//give player a card
	/*@ requires topCard != null;
	  @ requires players != null;
	  @ ensures remainingCards() == \old(remainingCards()) - 1;
	// @ ensures (\exists int i; 0 <= i && i < players.length;
	// @ 	\old(players[i]).getTotalCards() == players[i].getTotalCards() - 1);
	  @*/
	public void drawCard(/*@ non_null @*/ UNOCard topCard) {
		for (Player p : players) {
			if (p.isMyTurn()) {
				UNOCard newCard = getCard();
				p.obtainCard(newCard);
				if (!canPlay(topCard, newCard)) {
					switchTurn();
				}
				return;
			}
		}
	}

	/*@ requires players != null;
	  @ ensures (\forall int i; 0 <= i && i < players.length;
	  @ 	players[i] == \old(players[i]) && players[i] != null);
	  @*/
	public void switchTurn() {
		for (Player p : players) {
			p.toggleTurn();
		}
		whoseTurn();
	}

	//Draw cards x times
	/*@ requires times > 0;
	  @ assignable players[*];
	  @ ensures remainingCards() == \old(remainingCards()) - times;
	  @*/
	public void drawPlus(int times) {
		for (Player p : players) {
			if (!p.isMyTurn()) {
				for (int i = 1; i <= times; i++)
					p.obtainCard(getCard());
			}
		}
	}

	//response whose turn it is
	/*@ requires infoPanel != null;
	  @ assignable \nothing;
	  @*/
	public void whoseTurn() {

		for (Player p : players) {
			if (p.isMyTurn()){
				infoPanel.updateText(p.getName() + "'s Turn");
				System.out.println(p.getName() + "'s Turn");
			}
		}
		infoPanel.setDetail(playedCardsSize(), remainingCards());
		infoPanel.repaint();
	}

	//return if the game is over
	public boolean isOver() {

		if(cardStack.isEmpty()){
			isOver = true;
			return isOver;
		}

		for (Player p : players) {
			if (!p.hasCards()) {
				isOver = true;
				break;
			}
		}

		return isOver;
	}

	public /*@ pure @*/ int remainingCards() {
		return cardStack.size();
	}

	public int[] playedCardsSize() {
		int[] nr = new int[2];
		int i = 0;
		for (Player p : players) {
			nr[i] = p.totalPlayedCards();
			i++;
		}
		return nr;
	}

	//Check if this card can be played
	private /*@ pure @*/ boolean canPlay(/*@ non_null @*/ UNOCard topCard, /*@ non_null @*/ UNOCard newCard) {

		// Color or value matches
		if (topCard.getColor().equals(newCard.getColor())
				|| topCard.getValue().equals(newCard.getValue()))
			return true;
		// if chosen wild card color matches
		else if (topCard.getType() == WILD)
			return ((WildCard) topCard).getWildColor().equals(newCard.getColor());

		// suppose the new card is a wild card
		else if (newCard.getType() == WILD)
			return true;

		// else
		return false;
	}

	//Check whether the player said or forgot to say UNO
	public void checkUNO() {
		for (Player p : players) {
			if (p.isMyTurn()) {
				if (p.getTotalCards() == 1 && !p.getSaidUNO()) {
					infoPanel.setError(p.getName() + " Forgot to say UNO");
					p.obtainCard(getCard());
					p.obtainCard(getCard());
				}
			}
		}
	}

	public void setSaidUNO() {
		for (Player p : players) {
			if (p.isMyTurn()) {
				if (p.getTotalCards() == 2) {
					p.saysUNO();
					infoPanel.setError(p.getName() + " said UNO");
				}
			}
		}
	}

	public /*@ pure @*/ boolean isPCsTurn(){
		return pc.isMyTurn();
	}

	//if it's PC's turn, play it for pc
	public void playPC(/*@ non_null @*/ UNOCard topCard) {

		if (pc.isMyTurn()) {
			boolean done = pc.play(topCard);

			if(!done)
				drawCard(topCard);
		}
	}
}
