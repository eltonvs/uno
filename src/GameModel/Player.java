package GameModel;

import java.util.LinkedList;

import View.UNOCard;

public class Player {

	//@ public initially name != null;
	private /*@ spec_public nullable @*/ String name;
	private /*@ spec_public @*/ boolean isMyTurn = false;
	private /*@ spec_public @*/ boolean saidUNO = false;

	//@ public initially myCards != null;
	private /*@ spec_public nullable @*/ LinkedList<UNOCard> myCards;

	//@ public invariant playedCards >= 0;
	private /*@ spec_public @*/ int playedCards = 0;

	public Player(){
		myCards = new LinkedList<>();
	}

	/*@ requires player != null;
	  @ assignable name, myCards;
	  @ ensures name == player;
	  @ ensures myCards != null && myCards.size() == 0;
	  @*/
	public Player(/*@ non_null @*/ String player){
		setName(player);
		myCards = new LinkedList<>();
	}

	/*@ requires newName != null;
	  @ assignable this.name;
	  @ ensures this.name == newName;
	  @*/
	public void setName(/*@ non_null @*/ String newName){
		name = newName;
	}

	/*@ requires this.name != null;
	  @ ensures \result == this.name;
	  @*/
	public /*@ pure @*/ String getName(){
		return this.name;
	}

	/*@ requires card != null;
	  @ requires this.myCards != null;
	  @ assignable myCards;
	  @ ensures myCards.size() == \old(myCards.size()) + 1;
	  @ ensures myCards.get(myCards.size() - 1) == card;
	  @ ensures (\forall int i; 0 <= i && i < myCards.size() - 1;
	  @ 	myCards.get(i) == \old(myCards).get(i));
	  @*/
	public void obtainCard(/*@ non_null @*/ UNOCard card){
		myCards.add(card);
	}

	/*@ requires this.myCards!= null;
	  @ ensures this.myCards.size() >= 0;
	  @ ensures \result == this.myCards;
	  @ ensures (\forall int i; 0 <= i && i < this.myCards.size();
	  @ 	this.myCards.get(i) != null
	  @ 		&& this.myCards.get(i) instanceof UNOCard);
	  @*/
	public /*@ pure @*/ LinkedList<UNOCard> getAllCards(){
		return myCards;
	}

	/*@ requires this.myCards!= null;
	  @ ensures \result == myCards.size();
	  @*/
	public /*@ pure @*/ int getTotalCards(){
		return myCards.size();
	}

	/*@ requires thisCard != null;
	  @ requires this.myCards != null;
	  @ ensures \result
	  @ 	== (\exists int j; 0 <= j && j < myCards.size();
	  @ 		myCards.get(j) == thisCard);
	  @*/
	public /*@ pure @*/ boolean hasCard(/*@ non_null @*/ UNOCard thisCard){
		return myCards.contains(thisCard);
	}

	/*@ requires thisCard != null;
	  @ requires this.myCards != null;
	  @ assignable myCards, playedCards;
	  @ ensures myCards.size() == \old(myCards.size()) - 1;
	  @ ensures playedCards == \old(playedCards) + 1;
	  @*/
	public void removeCard(/*@ non_null @*/ UNOCard thisCard){
		myCards.remove(thisCard);
		playedCards++;
	}

	//@ ensures \result == playedCards;
	public /*@ pure @*/ int totalPlayedCards(){
		return playedCards;
	}

	/*@ assignable isMyTurn;
	  @ ensures isMyTurn != \old(isMyTurn) && (isMyTurn == true || isMyTurn == false);
	  @*/
	public void toggleTurn(){
		isMyTurn = (isMyTurn) ? false : true;
	}

	//@ ensures \result == isMyTurn;
	public /*@ pure @*/ boolean isMyTurn(){
		return isMyTurn;
	}

	//@ ensures \result == myCards.size() > 0;
	public /*@ pure @*/ boolean hasCards(){
		return (myCards.isEmpty()) ? false : true;
	}

	//@ ensures \result == saidUNO;
	public /*@ pure @*/ boolean getSaidUNO(){
		return saidUNO;
	}

	/*@ assignable saidUNO;
	  @ ensures saidUNO == true;
	  @*/
	public void saysUNO(){
		saidUNO = true;
	}

	/*@ assignable saidUNO;
	  @ ensures saidUNO == false;
	  @*/
	public void setSaidUNOFalse(){
		saidUNO = false;
	}

	/*@ assignable myCards;
	  @ ensures myCards != null && myCards.size() == 0;
	  @*/
	public void setCards(){
		myCards = new LinkedList<>();
	}
}
