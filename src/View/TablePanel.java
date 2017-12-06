package View;
import java.awt.Color;
import java.awt.Dimension;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;

import javax.swing.JPanel;

import CardModel.WildCard;
import Interfaces.GameConstants;

public class TablePanel extends JPanel implements GameConstants {

	/*@ public initially topCard != null;
	  @ public invariant topCard != null;
	  @*/
	private /*@ spec_public nullable @*/ UNOCard topCard;
	
	/*@ public initially table != null;
	  @ public invariant table != null;
	  @*/
	private /*@ spec_public nullable @*/ JPanel table;

	public TablePanel(UNOCard firstCard){
		setOpaque(false);
		setLayout(new GridBagLayout());

		topCard = firstCard;
		table = new JPanel();
		table.setBackground(new Color(64,64,64));

		setTable();
		setComponents();
	}

	private void setTable(){

		table.setPreferredSize(new Dimension(500,200));
		table.setLayout(new GridBagLayout());

		GridBagConstraints c = new GridBagConstraints();
		c.fill = GridBagConstraints.HORIZONTAL;
		c.gridx = 0;
		c.gridy = 0;
		table.add(topCard, c);
	}

	private void setComponents() {
		GridBagConstraints c = new GridBagConstraints();
		c.fill = GridBagConstraints.HORIZONTAL;
		c.gridx = 0;
		c.gridy = 0;
		c.insets = new Insets(0, 130, 0, 45);
		add(table,c);

		c.fill = GridBagConstraints.HORIZONTAL;
		c.anchor = GridBagConstraints.LINE_END;
		c.gridwidth = GridBagConstraints.REMAINDER;
		c.gridx = 1;
		c.gridy = 0;
		c.insets = new Insets(0, 1, 0, 1);
		add(infoPanel, c);
	}

	/*@ requires playedCard != null;
	  @ assignable topCard;
	  @ ensures topCard == playedCard;
	  @*/
	public void setPlayedCard(UNOCard playedCard){
		table.removeAll();
		topCard = playedCard;
		setTable();

		setBackgroundColor(playedCard);
	}

	/*@ requires playedCard != null;
	  @ requires playedCard.getType() == WILD || playedCard.getType() != WILD;
	  @*/
	public void setBackgroundColor(UNOCard playedCard){
		Color background;
		if(playedCard.getType()== WILD)
			background = ((WildCard) playedCard).getWildColor();
		else
			background = playedCard.getColor();

		table.setBackground(background);
	}
}
