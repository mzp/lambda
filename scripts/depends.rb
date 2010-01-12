puts 'digraph depend{'

ARGF.read.gsub(/\\\n/,'').each do|line|
  file,depends = line.split ':',2
  if file =~ /\.v/
    depends.split.each do |x|
      puts "#{File.basename file,'.*'} -> #{File.basename x,'.*'}"
    end
  end
end

puts '}'
