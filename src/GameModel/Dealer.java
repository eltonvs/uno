package GameModel;

import java.util.LinkedList;
import java.util.Random;
import java.util.Stack;

import CardModel.CardDeck;
import Interfaces.GameConstants;
import View.UNOCard;

public class Dealer implements GameConstants {

	//@ public initially cardDeck != null;
	private /*@ spec_public nullable @*/ CardDeck cardDeck;
	private /*@ spec_public nullable @*/ Stack<UNOCard> cardStack;

	public Dealer() {
		this.cardDeck = new CardDeck();
	}

	//Shuffle cards
	/*@ requires this.cardDeck != null;
	  @ ensures \result != null && \result == this.cardStack;
	  @ ensures this.cardDeck.getCards().size() == 0;
	  @ ensures this.cardStack.size() == \old(this.cardDeck.getCards().size());
	  @*/
	public Stack<UNOCard> shuffle() {

		LinkedList<UNOCard> deckOfCards = cardDeck.getCards();
		LinkedList<UNOCard> shuffledCards = new LinkedList<>();

		while (!deckOfCards.isEmpty()) {
			int totalCards = deckOfCards.size();

			Random random = new Random();
			int pos = random.nextInt(totalCards);

			UNOCard randomCard = deckOfCards.get(pos);
			deckOfCards.remove(pos);
			shuffledCards.add(randomCard);
		}

		cardStack = new Stack<>();
		for (UNOCard card : shuffledCards) {
			cardStack.add(card);
		}

		return cardStack;
	}

	//Spread cards to players - 8 each
	/*@ requires this.cardStack != null;
	  @ requires players != null && players.length > 0;
	  @ ensures this.cardStack.size() == \old(this.cardStack.size()) - players.length * FIRSTHAND;
	  @ ensures (\forall int i; 0 <= i && i < players.length;
	  @ 	players[i].getTotalCards() == FIRSTHAND);
	  @ ensures (\forall int i; 0 <= i && i < this.cardStack.size();
	  @ 	((Stack) this.cardStack).get(i) == ((Stack) \old(this.cardStack)).get(i));
	  @*/
	public void spreadOut(/*@ non_null @*/ Player[] players) {
		for (int i = 1; i <= FIRSTHAND; i++) {
			for (Player p : players) {
				p.obtainCard(cardStack.pop());
			}
		}
	}

	/*@ requires cardStack != null && cardStack.size() > 0;
	  @ assignable cardStack;
	  @ ensures \result != null && \result == \old(this.cardStack.peek());
	  @ ensures this.cardStack.size() == \old(this.cardStack.size()) - 1;
	  @ ensures (\forall int i; 0 <= i && i < this.cardStack.size();
	  @ 	((Stack) this.cardStack).get(i) == ((Stack) \old(this.cardStack)).get(i));
	  @*/
	public UNOCard getCard(){
		return cardStack.pop();
	}
}
