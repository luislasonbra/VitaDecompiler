TARGET = vitadecompiler
OBJS = main.o vita.o utils.o asprintf.o import/vita-import.o import/vita-import-parse.o import/yamltree.o import/yamltreeutil.o

LIBS = -lcapstone -lyaml

CFLAGS = -Wall -Wextra -std=c99 -std=c++0x

all: $(TARGET)

$(TARGET): $(OBJS)
	@echo "Creating binary $(TARGET)"
	$(CXX) $(OBJS) -o $@ $(LIBS)

%.o: %.cpp
	@echo "Compiling $^"
	$(CXX) $(CFLAGS) -c $^ -o $@

clean:
	@echo "Removing all the .o files"
	@$(RM) $(OBJS)

mrproper: clean
	@echo "Removing binary"
	@$(RM) $(TARGET)

install: all
	@cp $(TARGET) ../bin