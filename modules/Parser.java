import tlc2.value.IValue;
import tlc2.value.impl.*;

import java.io.*;
import java.util.*;

public class Parser {
  // @TLAPlusOperator(identifier = "parse", module = "Parser")
  public static IValue parse(final StringValue absolutePath) throws IOException {
    BufferedReader br = new BufferedReader(new FileReader(absolutePath.val.toString()));
    List<Value> values = new ArrayList<>();
    try {
      String line = br.readLine();
      while (line != null) {
        // split string on seperator
        String[] lnarr = line.split(", ");
        // [vals] will hold the tuple of values for each state
        List<Value> vals = new ArrayList<>();
        vals.add(IntValue.gen(Integer.parseInt(lnarr[0])));
        vals.add(
          lnarr[1].equals("a") ?
          ModelValue.make(lnarr[1]) :
          new BoolValue(Boolean.parseBoolean(lnarr[1])));
        // add the corresponding state tuple to the behavior
        values.add(new TupleValue(vals.toArray(new Value[0])));
        line = br.readLine();
      }
    } finally {
      br.close();
    }
    return new TupleValue(values.toArray(new Value[0]));
  }
}
