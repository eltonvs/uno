package View;
import java.awt.Color;
import java.awt.Dimension;
import java.awt.Font;
import java.awt.FontMetrics;
import java.awt.Graphics;

import javax.swing.JPanel;

public class InfoPanel extends JPanel {
	
	/*@ public initially error.equals("");
	  @*/
	private /*@ spec_public nullable @*/ String error;
	
	/*@ public initially text.equals("Game Started");
	  @ public invariant !text.equals("");
	  @*/
	private /*@ spec_public nullable @*/ String text;
	
	private /*@ spec_public @*/ int panelCenter;
	
	/*@ public initially you == 0;
	  @ public invariant you >= 0;
	  @*/
	private /*@ spec_public @*/ int you = 0;
	
	/*@ public initially pc == 0;
	  @ public invariant pc >= 0;
	  @*/
	private /*@ spec_public @*/ int pc = 0;
	
	/*@ public initially rest == 0;
	  @ public invariant rest >= 0;
	  @*/
	private /*@ spec_public @*/ int rest = 0;
	
	public InfoPanel(){
		setPreferredSize(new Dimension(275,200));
		setOpaque(false);
		error = "";
		text = "Game Started";
		
		updateText(text);
	}
	
	protected void paintComponent(Graphics g) {
		super.paintComponent(g);
		panelCenter = getWidth()/2;
		
		printMessage(g);
		printError(g);
		printDetail(g);
	}

 	//@ requires g != null;
	private void printError(Graphics g) {
		if(!error.isEmpty()){
			Font adjustedFont = new Font("Calibri", Font.PLAIN,	25);
			
			FontMetrics fm = this.getFontMetrics(adjustedFont);
			int xPos = panelCenter - fm.stringWidth(error) / 2;
			
			g.setFont(adjustedFont);
			g.setColor(Color.red);
			g.drawString(error, xPos, 35);
			
			error = "";
		}
	}

	private void printMessage(Graphics g) {
		Font adjustedFont = new Font("Calibri", Font.BOLD,	25);	
		
		//Determine the width of the word to position
		FontMetrics fm = this.getFontMetrics(adjustedFont);
		int xPos = panelCenter - fm.stringWidth(text) / 2;
		
		g.setFont(adjustedFont);
		g.setColor(new Color(228,108,10));
		g.drawString(text, xPos, 75);		
	}
	
	private void printDetail(Graphics g){
		Font adjustedFont = new Font("Calibri", Font.BOLD,	25);	
		FontMetrics fm = this.getFontMetrics(adjustedFont);
		g.setColor(new Color(127,127,127));
		
		//Determine the width of the word to position
		String text = "Played Cards";
		int xPos = panelCenter - fm.stringWidth(text) / 2;
		
		g.setFont(adjustedFont);
		g.drawString(text, xPos, 120);
		
		text = "Remaining: " + rest;
		xPos = panelCenter - fm.stringWidth(text) / 2;
		g.drawString(text, xPos, 180);
		
		//Details
		adjustedFont = new Font("Calibri", Font.PLAIN,	20);
		g.setFont(adjustedFont);
		fm = this.getFontMetrics(adjustedFont);
		
		text = "You : "+ you + "  PC : " + pc;
		xPos = panelCenter - fm.stringWidth(text) / 2;
		g.drawString(text, xPos, 140);
		
		text = String.valueOf(rest);
		xPos = panelCenter - fm.stringWidth(text) / 2;
		//g.drawString(text, xPos, 190);
	}


	/*@ assignable text;
	  @ ensures text == newText;
	  @*/
	public void updateText(String newText) {
		text = newText;
	}
	
	/*@ assignable error;
	  @ ensures error == errorMgs;
	  @*/
	public void setError(String errorMgs){
		error = errorMgs;
	}
	
	/*@ requires playedCards != null; 
	  @ assignable you, pc, rest;
 	  @ ensures you == playedCards[1];
	  @ ensures pc == playedCards[0];
	  @ ensures rest == remaining;
	  @*/
	public void setDetail(int[] playedCards, int remaining){
		you = playedCards[1];
		pc = playedCards[0];
		rest = remaining;
	}
}
