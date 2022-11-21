package ij.gui;
import ij.*;
import ij.process.*;
import java.awt.geom.*;

/**
 * A rectangular region of interest and superclass for the other ROI classes.
 *
 * This class implements {@code Iterable<Point>} and can thus be
 * used to iterate over the contained coordinates. Usage example:
 * <pre>
 * Roi roi = ...;
 * for (Point p : roi) {
 *   // process p
 * }
 * </pre>
 * <b>
 * Convention for subpixel resolution and zooming in:
 * </b><ul>
 * <li> Area ROIs: Integer coordinates refer to the top-left corner of the pixel with these coordinates.
 *      Thus, pixel (0,0) is enclosed by the rectangle spanned between points (0,0) and (1,1),
 *      i.e., a rectangle at (0,0) with width = height = 1 pixel.
 * <li> Line and Point Rois: Integer coordinates refer to the center of a pixel.
 *      Thus, a line from (0,0) to (1,0) has its start and end points in the center of
 *      pixels (0,0) and (1,0), respectively, and drawing the line should affect both
 *      pixels. For images dispplayed at high zoom levels, this means that (open) lines
 *      and single points are displayed 0.5 pixels further to the right and bottom than
 *      the outlines of area ROIs (closed lines) with the same coordinates.
 * </ul>
 * Note that rectangular and (nonrotated) oval ROIs do not support subpixel resolution.
 * Since ImageJ 1.52t, this convention does not depend on the Prefs.subpixelResolution
 * (previously accessible via Edit>Options>Plot) and this flag has no effect any more.
 *
  */
public class MoveHandle {

	public static final int CONSTRUCTING=0, MOVING=1, RESIZING=2, NORMAL=3, MOVING_HANDLE=4; // States
	public static final int RECTANGLE=0, OVAL=1, POLYGON=2, FREEROI=3, TRACED_ROI=4, LINE=5,
		POLYLINE=6, FREELINE=7, ANGLE=8, COMPOSITE=9, POINT=10; // Types
	public static final int HANDLE_SIZE = 5;  // replaced by getHandleSize()
	public static final int NOT_PASTING = -1;
	public static final int FERET_ARRAYSIZE = 16; // Size of array with Feret values
	public static final int FERET_ARRAY_POINTOFFSET = 8; // Where point coordinates start in Feret array


	static final int NO_MODS=0, ADD_TO_ROI=1, SUBTRACT_FROM_ROI=2; // modification states

	int startX, startY, x, y, width, height;
	double startXD, startYD;
	Rectangle2D.Double bounds;
	int activeHandle;
	int state;
	int modState = NO_MODS;
	int cornerDiameter;             //for rounded rectangle
	int previousSX, previousSY;     //remember for aborting moving with esc and constrain

	protected int type;
	protected int xMax, yMax;
	protected ImagePlus imp;
	protected ImageCanvas ic;
	protected int oldX, oldY, oldWidth, oldHeight;  //remembers previous clip rect
	protected int clipX, clipY, clipWidth, clipHeight;
	protected ImagePlus clipboard;
	protected boolean constrain;    // to be square or limit to horizontal/vertical motion
	protected boolean center;
	protected boolean aspect;
	protected boolean updateFullWindow;
	protected double mag = 1.0;
	protected double asp_bk;        //saves aspect ratio if resizing takes roi very small
	protected ImageProcessor cachedMask;

	protected boolean nonScalable;
	protected boolean overlay;
	protected boolean wideLine;
	protected boolean ignoreClipRect;
	protected double flattenScale = 1.0;


	public void moveHandle(int sx, int sy) {
		double asp;
		if (clipboard!=null) return;
		int ox = ic.offScreenX2(sx);
		int oy = ic.offScreenY2(sy);
		if (ox<0) ox=0; if (oy<0) oy=0;
		if (ox>xMax) ox=xMax; if (oy>yMax) oy=yMax;
		int x1=x, y1=y, x2=x1+width, y2=y+height, xc=x+width/2, yc=y+height/2;
		if (width > 7 && height > 7) {
			asp = (double)width/(double)height;
			asp_bk = asp;
		} else
			asp = asp_bk;

		switch (activeHandle) {
			case 0:
				x=ox; y=oy;
				break;
			case 1:
				y=oy;
				break;
			case 2:
				x2=ox; y=oy;
				break;
			case 3:
				x2=ox;
				break;
			case 4:
				x2=ox; y2=oy;
				break;
			case 5:
				y2=oy;
				break;
			case 6:
				x=ox; y2=oy;
				break;
			case 7:
				x=ox;
				break;
		}
		if (x<x2)
		   width=x2-x;
		else
		  {width=1; x=x2;}
		if (y<y2)
		   height = y2-y;
		else
		   {height=1; y=y2;}

		if (center) {
			switch (activeHandle){
				case 0:
					width=(xc-x)*2;
					height=(yc-y)*2;
					break;
				case 1:
					height=(yc-y)*2;
					break;
				case 2:
					width=(x2-xc)*2;
					x=x2-width;
					height=(yc-y)*2;
					break;
				case 3:
					width=(x2-xc)*2;
					x=x2-width;
					break;
				case 4:
					width=(x2-xc)*2;
					x=x2-width;
					height=(y2-yc)*2;
					y=y2-height;
					break;
				case 5:
					height=(y2-yc)*2;
					y=y2-height;
					break;
				case 6:
					width=(xc-x)*2;
					height=(y2-yc)*2;
					y=y2-height;
					break;
				case 7:
					width=(xc-x)*2;
					break;
			}
			if (x>=x2) {
				width=1;
				x=x2=xc;
			}
			if (y>=y2) {
				height=1;
				y=y2=yc;
			}
			bounds = null;
		}

		if (constrain) {
			if (activeHandle==1 || activeHandle==5)
				width=height;
			else
				height=width;

			if(x>=x2) {
				width=1;
				x=x2=xc;
			}
			if (y>=y2) {
				height=1;
				y=y2=yc;
			}
			switch (activeHandle) {
				case 0:
					x=x2-width;
					y=y2-height;
					break;
				case 1:
					x=xc-width/2;
					y=y2-height;
					break;
				case 2:
					y=y2-height;
					break;
				case 3:
					y=yc-height/2;
					break;
				case 5:
					x=xc-width/2;
					break;
				case 6:
					x=x2-width;
					break;
				case 7:
					y=yc-height/2;
					x=x2-width;
					break;
			}
			if (center) {
				x=xc-width/2;
				y=yc-height/2;
			}
		}

		if (aspect && !constrain) {
			if (activeHandle==1 || activeHandle==5) width=(int)Math.rint((double)height*asp);
			else height=(int)Math.rint((double)width/asp);

			switch (activeHandle){
				case 0:
					x=x2-width;
					y=y2-height;
					break;
				case 1:
					x=xc-width/2;
					y=y2-height;
					break;
				case 2:
					y=y2-height;
					break;
				case 3:
					y=yc-height/2;
					break;
				case 5:
					x=xc-width/2;
					break;
				case 6:
					x=x2-width;
					break;
				case 7:
					y=yc-height/2;
					x=x2-width;
					break;
			}
			if (center) {
				x=xc-width/2;
				y=yc-height/2;
			}

			// Attempt to preserve aspect ratio when roi very small:
			if (width<8) {
				if(width<1) width = 1;
				height=(int)Math.rint((double)width/asp_bk);
			}
			if (height<8) {
				if(height<1) height =1;
				width=(int)Math.rint((double)height*asp_bk);
			}
		}
	}

}
