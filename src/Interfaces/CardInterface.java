package Interfaces;

import java.awt.Color;
import java.awt.Dimension;

public interface CardInterface {
	//@ public model instance String val;
	//@ public model instance int typ;
	//@ public model instance Color col;

	/*@ public constraint \old(WIDTH) == WIDTH;
	  @*/
	/*@ spec_public @*/ int WIDTH = 50;

	/*@ public constraint \old(HEIGHT) == HEIGHT;
	  @*/
	/*@ spec_public @*/ int HEIGHT = 75;
	/*@ spec_public non_null @*/ Dimension SMALL = new Dimension(WIDTH, HEIGHT);
	/*@ spec_public non_null @*/ Dimension MEDIUM = new Dimension(WIDTH * 2, HEIGHT * 2);
	/*@ spec_public non_null @*/ Dimension BIG = new Dimension(WIDTH * 3, HEIGHT * 3);

	// Default card size
	/*@ public invariant CARDSIZE == MEDIUM;
	  @*/
	/*@ spec_public non_null @*/ Dimension CARDSIZE = MEDIUM;

	// Default offset
	/*@ public constraint \old(OFFSET) == OFFSET;
	  @*/
	/*@ spec_public @*/ int OFFSET = 71;

	/*@ requires newColor != null;
	  @ ensures col == newColor;
	  @*/
	void setColor(/*@ non_null @*/ Color newColor);

	/*@ ensures \result == col;
	  @*/
	/*@ pure @*/ Color getColor();

	/*@ requires newValue != null;
	  @ ensures val == newValue;
	  @*/
	void setValue(/*@ non_null @*/ String newValue);

	/*@ ensures \result == val;
	  @*/
	/*@ pure @*/ String getValue();

	/*@ requires newType == UNOConstants.NUMBERS || newType == UNOConstants.ACTION || newType == UNOConstants.WILD;
	  @ ensures typ == newType;
	  @*/
	void setType(int newType);

	/*@ ensures \result == UNOConstants.NUMBERS || \result == UNOConstants.ACTION || \result == UNOConstants.WILD;
	  @ ensures \result == typ;
	  @*/
	/*@ pure @*/ int getType();
}
