package CardModel;

import java.awt.Color;

import View.UNOCard;

public class WildCard extends UNOCard {

	private /*@ spec_public nullable @*/ Color chosenColor;

	public WildCard() {
	}

	public WildCard(String cardValue){
		super(BLACK, WILD, cardValue);
	}

	/*@ requires wildColor != null;
	  @ assignable chosenColor;
	  @ ensures chosenColor == wildColor;
	  @*/
	public void useWildColor(Color wildColor){
		chosenColor = wildColor;
	}

	/*@ requires chosenColor != null;
	  @ ensures \result == chosenColor;
	  @*/
	public /*@ pure @*/ Color getWildColor(){
		return chosenColor;
	}

}
